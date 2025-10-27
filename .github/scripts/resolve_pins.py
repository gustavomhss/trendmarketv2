import re,os,sys,json,subprocess,urllib.request
FALLBACKS={
  "actions/checkout":"v4.2.2",
  "actions/upload-artifact":"v4",
  "actions/download-artifact":"v4",
  "actions/setup-python":"v5.3.0",
  "actions/cache":"v4",
  "actions/github-script":"v7"
}
pat_inline=re.compile(r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
pat_key=re.compile(r'^\s*(?:-\s*)?uses:\s*$')
pat_val=re.compile(r'^\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')

def gh(url, token=None):
  req=urllib.request.Request(url,headers={"User-Agent":"pin-sweep","Authorization":f"Bearer {token}"} if token else {"User-Agent":"pin-sweep"})
  try:
    with urllib.request.urlopen(req) as r:
      return json.load(r)
  except Exception:
    return None

def resolve(owner_repo, ref, token=None):
  # already SHA?
  if re.fullmatch(r"[0-9a-fA-F]{40}", ref):
    j=gh(f"https://api.github.com/repos/{owner_repo}/commits/{ref}", token)
    if j and j.get('sha'):
      return ref
    return ref
  # commit
  j=gh(f"https://api.github.com/repos/{owner_repo}/commits/{ref}", token)
  if j and j.get('sha'): return j['sha']
  # tag peel
  t=gh(f"https://api.github.com/repos/{owner_repo}/git/refs/tags/{ref}", token)
  if t:
    arr=[t] if isinstance(t,dict) else t
    for e in arr:
      sha=e.get('object',{}).get('sha'); typ=e.get('object',{}).get('type')
      if sha:
        if typ=='tag':
          tag=gh(f"https://api.github.com/repos/{owner_repo}/git/tags/{sha}", token)
          peeled=tag and tag.get('object',{}).get('sha')
          if peeled: return peeled
        return sha
  # branch head
  h=gh(f"https://api.github.com/repos/{owner_repo}/git/refs/heads/{ref}", token)
  if h:
    arr=[h] if isinstance(h,dict) else h
    for e in arr:
      sha=e.get('object',{}).get('sha')
      if sha: return sha
  # fallback known
  fb=FALLBACKS.get(owner_repo)
  if fb and fb!=ref:
    return resolve(owner_repo, fb, token)
  return None

files=[]
for d,_,fs in os.walk('.github'):
  for f in fs:
    if f.endswith(('.yml','.yaml')):
      files.append(os.path.join(d,f))
files.sort()
GITHUB_TOKEN=os.environ.get('GITHUB_TOKEN') or os.environ.get('GH_TOKEN')
report=[]; mapping={}
for path in files:
  L=open(path,'r',encoding='utf-8',errors='ignore').read().splitlines(True)
  out=[]; i=0; changed=False
  while i<len(L):
    ln=L[i]
    m=pat_inline.match(ln)
    if m:
      q,a,r=m.groups()
      if not (a.startswith('./') or a.startswith('docker://')):
        sha=resolve(a,r,GITHUB_TOKEN)
        if sha and r!=sha:
          ln=re.sub(r'@[^"\'"\s#]+', '@'+sha, ln); changed=True
          report.append(('PIN',a,r,sha,path))
        elif not sha:
          report.append(('FAIL',a,r,'',path))
        else:
          report.append(('OK',a,r,'',path))
      out.append(ln); i+=1; continue
    if pat_key.match(ln) and i+1<len(L):
      v=L[i+1]; m2=pat_val.match(v)
      if m2:
        q,a,r=m2.groups()
        if not (a.startswith('./') or a.startswith('docker://')):
          sha=resolve(a,r,GITHUB_TOKEN)
          if sha and r!=sha:
            v=re.sub(r'@[^"\'"\s#]+','@'+sha,v); changed=True
            report.append(('PIN',a,r,sha,path))
          elif not sha:
            report.append(('FAIL',a,r,'',path))
          else:
            report.append(('OK',a,r,'',path))
        out.append(ln); out.append(v); i+=2; continue
    out.append(ln); i+=1
  if changed:
    open(path,'w',encoding='utf-8').write(''.join(out))

# lock
for kind,a,old,new,p in report:
  if kind in ('PIN','OK'):
    mapping[a]=new or old
open('.pins.report','w',encoding='utf-8').write('\n'.join('\t'.join(x) for x in report))
open('actions.lock','w',encoding='utf-8').write('actions:\n'+'\n'.join(f'  {k}: {v}' for k,v in sorted(mapping.items()))+f"\nmetadata:\n  updated_at: ")
