/* Test-only instrumentation, injected by the local regression server. */
window.__mobileProbe = {started: performance.now(), fetches: [], hover: [], events: [], long: [], errors: [], search: []};
const probe = window.__mobileProbe;
const originalMedia = window.matchMedia.bind(window);
window.matchMedia = q => q === '(hover: none), (pointer: coarse)'
  ? {matches: true, addEventListener() {}, removeEventListener() {}} : originalMedia(q);
const originalFetch = window.fetch.bind(window);
window.fetch = async (...args) => {
  const start = performance.now();
  if (String(args[0]).includes('/types/')) await new Promise(r => setTimeout(r, 500));
  const response = await originalFetch(...args);
  probe.fetches.push({url: String(args[0]), ms: Math.round(performance.now() - start)});
  return response;
};
window.addEventListener('error', e => probe.errors.push(e.message));
window.addEventListener('unhandledrejection', e => probe.errors.push(String(e.reason)));
try { new PerformanceObserver(list => probe.long.push(...list.getEntries().map(e =>
  ({start: Math.round(e.startTime), ms: Math.round(e.duration)})))).observe({type: 'longtask', buffered: true}); } catch (_) {}
document.addEventListener('pointerdown', e => {
  probe.last = performance.now(); probe.events.push({event: 'down', text: e.target.textContent.slice(0,40)});
}, true);
document.addEventListener('DOMContentLoaded', () => {
  probe.ready = Math.round(performance.now() - probe.started);
  // Simulated pointer capability must also expose touch-only action affordances.
  const style = document.createElement('style');
  style.textContent = '.has-definition-link{padding-right:2.5rem}.type-definition-link:not([hidden]){display:grid;position:absolute;right:.25rem;top:0;bottom:0;align-items:center;padding:.4rem}.type-definition-link svg{width:1.25rem;height:1.25rem;fill:none;stroke:currentColor}';
  document.head.appendChild(style);
  let searchHidden = document.body.classList.contains('mobile-search-hidden');
  new MutationObserver(records => {
    for (const record of records) {
      for (const node of record.addedNodes) if (node.nodeType === 1 && node.matches('.name-hover-popup'))
        probe.hover.push({phase: 'shell', ms: Math.round(performance.now() - probe.last)});
      if (record.attributeName === 'aria-busy' && record.target.matches('.name-hover-popup') && !record.target.hasAttribute('aria-busy'))
        probe.hover.push({phase: 'ready', ms: Math.round(performance.now() - probe.last)});
      const hidden = document.body.classList.contains('mobile-search-hidden');
      if (record.target === document.body && hidden !== searchHidden) {
        searchHidden = hidden; probe.search.push({hidden, at: performance.now()});
      }
    }
  }).observe(document.body, {childList: true, subtree: true, attributes: true, attributeFilter: ['aria-busy','class']});
});
