/* Bedrock reader: guide. AGPL-3.0-only. */

/* Keep the glossary useful as it grows: filtering is local and does not alter navigation. */
(function () {
  "use strict";
  document.addEventListener("DOMContentLoaded", function () {
    const input = document.querySelector("[data-term-search-input]");
    const list = document.querySelector(".term-glossary-list");
    if (!input || !list) return;
    const entries = [...list.querySelectorAll("[data-term-entry]")];
    const empty = document.querySelector("[data-term-empty]");
    function filter() {
      const query = input.value.trim().toLocaleLowerCase();
      let visible = 0;
      entries.forEach(function (entry) {
        const shown = !query || entry.dataset.termSearch.toLocaleLowerCase().includes(query);
        entry.hidden = !shown;
        if (shown) visible += 1;
      });
      if (empty) empty.hidden = visible !== 0;
    }
    input.addEventListener("input", filter);
  });
})();

/* The landing page keeps routes, the dependency map, milestones and the glossary in one place. */
(function () {
  "use strict";
  document.addEventListener("DOMContentLoaded", function () {
    const list = document.querySelector(".book-tabs");
    if (!list) return;
    const tabs = [...list.querySelectorAll("[data-panel]")];
    const panels = tabs.map(tab => document.getElementById(tab.dataset.panel));
    let active = null;
    const scrolls = new Map();
    list.setAttribute("role", "tablist");
    tabs.forEach((tab, i) => {
      tab.setAttribute("role", "tab");
      tab.setAttribute("aria-controls", panels[i].id);
      panels[i].setAttribute("role", "tabpanel");
      panels[i].setAttribute("aria-labelledby", tab.id);
      panels[i].tabIndex = 0;
    });
    function activate(id, updateHistory, restoreScroll) {
      const index = panels.findIndex(panel => panel.id === id);
      if (index < 0) return;
      if (active) scrolls.set(active, window.scrollY);
      active = id;
      document.querySelectorAll(".reading-guide a").forEach(link => {
        if (new URL(link.href).hash === `#${id}`) link.setAttribute("aria-current", "location");
        else link.removeAttribute("aria-current");
      });
      tabs.forEach((tab, i) => {
        const selected = i === index;
        tab.setAttribute("aria-selected", String(selected));
        tab.tabIndex = selected ? 0 : -1;
        panels[i].hidden = !selected;
      });
      if (updateHistory && location.hash !== `#${id}`) history.pushState(null, "", `#${id}`);
      document.querySelectorAll("#lang-switch a").forEach(link => {
        const url = new URL(link.href); url.hash = id; link.href = url.href;
      });
      document.dispatchEvent(new CustomEvent("bedrock:tabchange", { detail: { id } }));
      if (restoreScroll) requestAnimationFrame(() => window.scrollTo({
        top: scrolls.get(id) ?? Math.min(window.scrollY, list.offsetTop), behavior: "instant"
      }));
    }
    function fromHash() {
      let id;
      try { id = decodeURIComponent(location.hash.slice(1)); } catch (_) { id = ""; }
      const target = document.getElementById(id);
      const panel = panels.find(p => p === target || (target && p.contains(target)));
      activate(panel ? panel.id : "milestones", false, false);
      if (target && target !== panel) requestAnimationFrame(() => target.scrollIntoView());
    }
    tabs.forEach((tab, i) => {
      tab.addEventListener("click", e => {
        if (e.ctrlKey || e.metaKey || e.shiftKey || e.altKey || e.button !== 0) return;
        e.preventDefault(); activate(tab.dataset.panel, true, true);
      });
      tab.addEventListener("keydown", e => {
        let next;
        if (e.key === "ArrowRight") next = (i + 1) % tabs.length;
        else if (e.key === "ArrowLeft") next = (i + tabs.length - 1) % tabs.length;
        else if (e.key === "Home") next = 0;
        else if (e.key === "End") next = tabs.length - 1;
        else if (e.key === " ") next = i;
        else return;
        e.preventDefault(); tabs[next].focus(); activate(tabs[next].dataset.panel, true, true);
      });
    });
    document.addEventListener("click", e => {
      if (e.ctrlKey || e.metaKey || e.shiftKey || e.altKey || e.button !== 0) return;
      const link = e.target.closest("a[href]");
      if (!link || list.contains(link)) return;
      const url = new URL(link.href);
      if (url.origin !== location.origin || url.pathname !== location.pathname || !url.hash) return;
      let id;
      try { id = decodeURIComponent(url.hash.slice(1)); } catch (_) { return; }
      const target = document.getElementById(id);
      const panel = panels.find(p => p === target || (target && p.contains(target)));
      if (!panel) return;
      e.preventDefault(); activate(panel.id, false, false);
      history.pushState(null, "", url.hash);
      requestAnimationFrame(() => target.scrollIntoView());
    });
    window.addEventListener("hashchange", fromHash);
    window.addEventListener("popstate", fromHash);
    fromHash();
  });
})();

/* A schematic contraction of entire fibre pairs: domain point and path move together. */
