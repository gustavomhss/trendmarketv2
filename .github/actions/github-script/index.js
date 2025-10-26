const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const { createRequire } = require('node:module');

const inputScript = process.env['INPUT_SCRIPT'];

if (!inputScript || !inputScript.trim()) {
  console.error('Input "script" is required.');
  process.exit(1);
}

const summaryPath = process.env['GITHUB_STEP_SUMMARY'];
const token = process.env['GITHUB_TOKEN'];
const repoEnv = process.env['GITHUB_REPOSITORY'] || '';
const eventName = process.env['GITHUB_EVENT_NAME'] || '';
const eventPath = process.env['GITHUB_EVENT_PATH'];

let owner = '';
let repo = '';
if (repoEnv.includes('/')) {
  [owner, repo] = repoEnv.split('/', 2);
}

let eventPayload = {};
if (eventPath && fs.existsSync(eventPath)) {
  try {
    const raw = fs.readFileSync(eventPath, 'utf8');
    eventPayload = JSON.parse(raw);
  } catch (error) {
    console.warn(`Unable to parse event payload: ${error.message}`);
  }
}

const resolveIssueNumber = () => {
  if (!eventPayload || typeof eventPayload !== 'object') {
    return undefined;
  }
  if (eventPayload.issue && typeof eventPayload.issue.number === 'number') {
    return eventPayload.issue.number;
  }
  if (eventPayload.pull_request && typeof eventPayload.pull_request.number === 'number') {
    return eventPayload.pull_request.number;
  }
  if (typeof eventPayload.number === 'number') {
    return eventPayload.number;
  }
  return undefined;
};

const defaultIssueNumber = resolveIssueNumber();

const summaryBuffer = [];

const summary = {
  addHeading(text, level = 1) {
    const headingLevel = Math.max(1, Number(level) || 1);
    summaryBuffer.push(`${'#'.repeat(headingLevel)} ${text}\n`);
    return this;
  },
  addRaw(text) {
    summaryBuffer.push(String(text));
    return this;
  },
  addEOL() {
    summaryBuffer.push('\n');
    return this;
  },
  async write(options = {}) {
    if (!summaryPath) {
      console.warn('GITHUB_STEP_SUMMARY is not defined.');
      summaryBuffer.length = 0;
      return this;
    }
    const content = summaryBuffer.join('');
    summaryBuffer.length = 0;
    const flag = options.overwrite ? 'w' : 'a';
    await fs.promises.mkdir(path.dirname(summaryPath), { recursive: true }).catch(() => undefined);
    await fs.promises.writeFile(summaryPath, content, { encoding: 'utf8', flag });
    return this;
  },
};

const core = {
  warning(message) {
    console.warn(message);
  },
  summary,
};

const github = {
  rest: {
    issues: {
      async createComment({ owner: inputOwner, repo: inputRepo, issue_number, body }) {
        const resolvedOwner = inputOwner || owner;
        const resolvedRepo = inputRepo || repo;
        const resolvedIssue = typeof issue_number === 'number' ? issue_number : defaultIssueNumber;

        if (!token) {
          throw new Error('GITHUB_TOKEN is required to create comments.');
        }
        if (!resolvedOwner || !resolvedRepo || !resolvedIssue) {
          throw new Error('Repository owner, name, or issue number missing for comment.');
        }
        const response = await fetch(`https://api.github.com/repos/${resolvedOwner}/${resolvedRepo}/issues/${resolvedIssue}/comments`, {
          method: 'POST',
          headers: {
            'Authorization': `Bearer ${token}`,
            'Accept': 'application/vnd.github+json',
            'Content-Type': 'application/json',
            'User-Agent': 'trendmarketv2-local-github-script',
          },
          body: JSON.stringify({ body: String(body ?? '') }),
        });

        if (!response.ok) {
          const errorBody = await response.text().catch(() => '');
          throw new Error(`Failed to create comment: ${response.status} ${response.statusText} ${errorBody}`.trim());
        }

        return response.json();
      },
    },
  },
};

const context = {
  eventName,
  repo: { owner, repo },
  issue: { number: defaultIssueNumber },
};

const sandboxRequire = createRequire(__filename);
const sandbox = {
  require: sandboxRequire,
  module: { exports: {} },
  exports: {},
  core,
  github,
  context,
  console,
  process,
  __filename,
  __dirname: __dirname,
  Buffer,
  setTimeout,
  setInterval,
  clearTimeout,
  clearInterval,
};

(async () => {
  const wrapped = `(async () => {\n${inputScript}\n})()`;
  const script = new vm.Script(wrapped, { filename: 'workflow-script.js' });
  try {
    const result = script.runInNewContext(sandbox, { timeout: 0 });
    if (result && typeof result.then === 'function') {
      await result;
    }
  } catch (error) {
    console.error(error && error.stack ? error.stack : String(error));
    process.exitCode = 1;
  }
})();
