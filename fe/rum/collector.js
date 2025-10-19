const endpoint = '/collect';
const env = window.__RUM_ENV__ || 'local';
const page = window.location.pathname || 'unknown';

let maxLatency = 0;
let maxId = '';

if ('PerformanceObserver' in window) {
  const observer = new PerformanceObserver((list) => {
    const entries = list.getEntries();
    for (const entry of entries) {
      if (entry.duration > maxLatency) {
        maxLatency = entry.duration;
        maxId = entry.identifier || entry.name;
      }
    }
  });
  observer.observe({ type: 'event', buffered: true });

  window.addEventListener('beforeunload', () => {
    const payload = JSON.stringify({
      name: 'INP',
      value: Math.round(maxLatency),
      id: maxId,
      env,
      page,
      ts: Date.now(),
    });
    navigator.sendBeacon(endpoint, payload);
  });
}
