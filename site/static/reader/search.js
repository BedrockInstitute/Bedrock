/* Bedrock reader: search. AGPL-3.0-only. */
import { cfg } from "./document.js";

  /* Search chapters as well as Agda names; share one retryable index request. */
  function initSearch() {
    const box = document.getElementById('search-box'), out = document.getElementById('search-results');
    if (!box || !out) return;
    const words = {
      en: { loading: 'Searching…', empty: 'No matching content.', error: 'Search could not load. Tap here to retry.', chapter: 'Chapter', definition: 'Definition' },
      zh: { loading: '正在搜索…', empty: '没有匹配的内容。', error: '搜索暂时无法载入，点击重试。', chapter: '章节', definition: '定义' },
      ja: { loading: '検索中…', empty: '一致する内容はありません。', error: '検索を読み込めません。クリックして再試行。', chapter: '章', definition: '定義' }
    }[cfg.lang] || { loading: 'Searching…', empty: 'No results.', error: 'Retry search', chapter: 'Chapter', definition: 'Definition' };
    let selected = -1, shown = [], revision = 0, worker = null, jobId = 0;
    const jobs = new Map();
    box.setAttribute('role', 'combobox'); box.setAttribute('aria-autocomplete', 'list');
    box.setAttribute('aria-controls', out.id); box.setAttribute('aria-expanded', 'false');
    const status = document.createElement('div'); status.className = 'sr-only'; status.setAttribute('role', 'status');
    box.parentNode.append(status);
    function close() { revision++; out.hidden = true; box.setAttribute('aria-expanded', 'false'); box.removeAttribute('aria-activedescendant'); }
    function open() { out.hidden = false; box.setAttribute('aria-expanded', 'true'); }
    function message(text, retry = false) {
      shown = []; selected = -1; box.removeAttribute('aria-activedescendant');
      out.replaceChildren(); const item = document.createElement(retry ? 'button' : 'p');
      item.className = 'search-message'; item.textContent = text;
      if (retry) { item.type = 'button'; item.addEventListener('click', run); }
      out.append(item); status.textContent = text; open();
    }
    function load(query) {
      if (!worker) {
        worker = new Worker(new URL('../search-worker.js', import.meta.url));
        worker.onmessage = event => {
          const job = jobs.get(event.data.id); if (!job) return;
          jobs.delete(event.data.id);
          if (event.data.error) job.reject(new Error('Search unavailable')); else job.resolve(event.data.results);
        };
        worker.onerror = () => {
          worker.terminate(); worker = null;
          jobs.forEach(job => job.reject(new Error('Search unavailable'))); jobs.clear();
        };
      }
      return new Promise((resolve, reject) => {
        const id = ++jobId; jobs.set(id, { resolve, reject });
        worker.postMessage({ id, query, lang: cfg.lang, url: new URL(cfg.baseUrl + '/search-content.json', location.href).href });
      });
    }
    function select(index) {
      selected = index;
      [...out.querySelectorAll('.res')].forEach((item, i) => {
        item.classList.toggle('sel', i === selected); item.setAttribute('aria-selected', String(i === selected));
      });
      const active = out.querySelector('.sel');
      if (active) { box.setAttribute('aria-activedescendant', active.id); active.scrollIntoView({ block: 'nearest' }); }
      else box.removeAttribute('aria-activedescendant');
    }
    async function run() {
      const request = ++revision, q = box.value.trim().slice(0, 200); selected = -1;
      if (!q) { close(); return; }
      message(words.loading);
      let matches;
      try { matches = await load(q); } catch (_) { if (request === revision) message(words.error, true); return; }
      if (request !== revision) return;
      shown = matches.map(entry => ({ ...entry,
        href: cfg.baseUrl + '/' + (entry.lang === '*' ? cfg.lang : entry.lang) + '/' + entry.href }));
      if (!shown.length) { message(words.empty); return; }
      out.replaceChildren(...shown.map((entry, i) => {
        const a = document.createElement('a'); a.className = 'res'; a.href = entry.href;
        a.id = 'search-result-' + i; a.setAttribute('role', 'option'); a.setAttribute('aria-selected', 'false');
        const name = document.createElement('span'); name.className = 'nm'; name.textContent = entry.name;
        const mod = document.createElement('span'); mod.className = 'mod';
        mod.textContent = (entry.lang === '*' ? 'Agda' : {en: 'English', zh: '中文', ja: '日本語'}[entry.lang]) + ' · ' + entry.module;
        a.append(name, mod);
        if (entry.type) { const type = document.createElement('span'); type.className = 'ty'; type.textContent = entry.type; a.append(type); }
        return a;
      }));
      box.removeAttribute('aria-activedescendant'); status.textContent = shown.length + ' ' + words.chapter + ' / ' + words.definition;
      open();
    }
    box.addEventListener('input', event => { if (!event.isComposing) run(); });
    box.addEventListener('compositionend', run);
    box.addEventListener('focus', () => { if (box.value.trim()) run(); });
    box.addEventListener('keydown', event => {
      if (event.isComposing) return;
      if (event.key === 'Escape') { close(); event.preventDefault(); return; }
      if (out.hidden || !shown.length) return;
      if (event.key === 'ArrowDown') { select(Math.min(selected + 1, shown.length - 1)); event.preventDefault(); }
      else if (event.key === 'ArrowUp') { select(Math.max(selected - 1, 0)); event.preventDefault(); }
      else if (event.key === 'Enter') { event.preventDefault(); location.href = shown[Math.max(selected, 0)].href; }
    });
    document.addEventListener('click', event => { if (!out.contains(event.target) && event.target !== box) close(); });
    box.parentNode.addEventListener('focusout', event => { if (!box.parentNode.contains(event.relatedTarget)) close(); });
  }

export { initSearch };
