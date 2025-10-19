import http from 'k6/http';
import { check, sleep } from 'k6';

export const options = {
  scenarios: {
    constant: {
      executor: 'constant-arrival-rate',
      rate: 120,
      duration: '60m',
      timeUnit: '1s',
      preAllocatedVUs: 60,
      maxVUs: 240,
    },
  },
  thresholds: {
    http_req_failed: ['rate==0'],
    http_req_duration: ['p(95)<=800'],
  },
};

export default function () {
  const res = http.get(`${__ENV.DEC_ENDPOINT || 'http://localhost:8080'}/decisions`);
  check(res, {
    'status 200': (r) => r.status === 200,
  });
  sleep(0.01);
}
