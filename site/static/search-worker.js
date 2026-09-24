/* Shared trilingual search. Index loading, normalization and ranking stay off the UI thread. */
'use strict';
let records = null, loading = null, newest = 0;
const normalized = text => (text || '').normalize('NFKC').toLocaleLowerCase().replace(/\s+/g, ' ').trim();
function rank(query, entry) {
  const name = entry._name, text = entry._text, module = entry._module;
  if (name === query) return entry.kind === 'chapter' ? 1200 : 1100;
  if (module === query) return entry.kind === 'chapter' ? 1150 : 400;
  const words = query.split(' ');
  if (!words.every(word => entry._all.includes(word))) return -1;
  if (name.startsWith(query)) return 900;
  if (name.includes(query)) return 800;
  if (text.includes(query)) return 600 + (entry.kind === 'term' ? 80 : 0);
  return 300;
}
async function load(url) {
  if (records) return records;
  if (!loading) loading = fetch(url).then(response => {
    if (!response.ok) throw new Error('Index unavailable'); return response.json();
  }).then(data => {
    if (!Array.isArray(data)) throw new Error('Invalid search index');
    records = data.map(entry => ({ ...entry, _name: normalized(entry.name),
      _module: normalized(entry.module), _text: normalized(entry.text),
      _all: normalized([entry.name, entry.module, entry.text].join(' ')) }));
    return records;
  }).finally(() => { loading = null; });
  return loading;
}
self.onmessage = async event => {
  const { id, query, url, lang } = event.data;
  newest = id;
  try {
    const index = await load(url), q = normalized(query), best = new Map();
    if (id !== newest) { self.postMessage({ id, results: [] }); return; }
    for (const entry of index) {
      const score = rank(q, entry);
      if (score < 0) continue;
      const key = entry.lang + ':' + entry.href;
      const previous = best.get(key);
      if (!previous || score > previous.score) best.set(key, { entry, score });
    }
    const result = [...best.values()].sort((a, b) => b.score - a.score ||
      Number(b.entry.lang === lang) - Number(a.entry.lang === lang)).slice(0, 40).map(({ entry }) => {
      const { _name, _module, _text, _all, ...publicEntry } = entry;
      const hit = _text.indexOf(q), start = Math.max(0, hit - 70);
      publicEntry.type = (start ? '…' : '') + entry.text.slice(start, start + 240) + (entry.text.length > start + 240 ? '…' : '');
      return publicEntry;
    });
    self.postMessage({ id, results: result });
  } catch (_) { self.postMessage({ id, error: true }); }
};
