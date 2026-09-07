/* Bedrock site behaviour: theme toggle, KaTeX rendering, type-on-hover, search.
 *
 * The type-on-hover mechanism is modelled on the 1lab's highlight-hover (AGPL-3.0,
 * https://1lab.dev) but reimplemented for Bedrock's `types/<Module>.json` sidecars.
 * Vanilla JS, no build step. See NOTICE.
 */
(function () {
  "use strict";
  var cfg = window.bedrock || { baseUrl: "", lang: "en", module: "" };

  /* ---- theme (light / dark / system) -------------------------------------- */
  var root = document.documentElement;
  function applyTheme(t) {
    root.classList.remove("theme-light", "theme-dark");
    if (t === "light") root.classList.add("theme-light");
    else if (t === "dark") root.classList.add("theme-dark");
  }
  function storedTheme() {
    try { return localStorage.getItem("bedrock-theme") || "system"; } catch (_) { return "system"; }
  }
  applyTheme(storedTheme());
  document.addEventListener("DOMContentLoaded", function () {
    try { localStorage.setItem("bedrock-lang", cfg.lang); } catch (e) {}
    var btn = document.getElementById("theme-toggle");
    if (btn) btn.addEventListener("click", function () {
      var order = ["system", "light", "dark"];
      var cur = storedTheme();
      var next = order[(order.indexOf(cur) + 1) % order.length];
      try { localStorage.setItem("bedrock-theme", next); } catch (_) {}
      applyTheme(next);
    });
    renderMath();
    initSearch();
    initHover();
    initOccur();
    initNav();
  });

  /* ---- mobile navigation drawer ------------------------------------------- */
  function initNav() {
    var body = document.body;
    var toggle = document.getElementById("nav-toggle");
    var toc = document.getElementById("toc");
    if (!toggle || !toc) return;
    var backdrop = document.getElementById("nav-backdrop");
    var close = document.getElementById("nav-close");
    function setOpen(open) {
      var wasOpen = body.classList.contains("nav-open");
      body.classList.toggle("nav-open", open);
      toggle.setAttribute("aria-expanded", open ? "true" : "false");
      if (backdrop) backdrop.hidden = !open;
      if (open && close) close.focus();
      else if (wasOpen) toggle.focus();
    }
    toggle.addEventListener("click", function () {
      setOpen(!body.classList.contains("nav-open"));
    });
    if (backdrop) backdrop.addEventListener("click", function () { setOpen(false); });
    if (close) close.addEventListener("click", function () { setOpen(false); });
    document.addEventListener("keydown", function (e) {
      if (e.key === "Escape") setOpen(false);
      if (e.key === "Tab" && body.classList.contains("nav-open")) {
        var items = Array.from(toc.querySelectorAll("button, summary, a[href]"))
          .filter(function (item) { return item.getClientRects().length > 0; });
        var first = items[0], last = items[items.length - 1];
        if (e.shiftKey && document.activeElement === first) { e.preventDefault(); last.focus(); }
        else if (!e.shiftKey && document.activeElement === last) { e.preventDefault(); first.focus(); }
      }
    });
    /* Tapping any link in the drawer navigates, so dismiss the drawer with it. */
    toc.addEventListener("click", function (e) {
      if (e.target.closest("a")) setOpen(false);
    });
    /* Leaving narrow layout (e.g. rotate to landscape) must not strand an open drawer. */
    var wide = window.matchMedia("(min-width: 60rem)");
    (wide.addEventListener ? wide.addEventListener.bind(wide, "change")
                           : wide.addListener.bind(wide))(function (e) {
      if (e.matches) setOpen(false);
    });
  }

  /* ---- math (client-side KaTeX over pre-wrapped spans) -------------------- */
  function renderMath() {
    if (typeof katex === "undefined") return;
    document.querySelectorAll(".math").forEach(function (el) {
      var disp = el.classList.contains("display");
      var tex = el.textContent.trim().replace(/^\${1,2}/, "").replace(/\${1,2}$/, "");
      try { katex.render(tex, el, { displayMode: disp, throwOnError: false }); }
      catch (e) { /* leave the source text in place on error */ }
    });
  }

  /* ---- type-on-hover ------------------------------------------------------ */
  var typeCache = {};
  function fetchTypes(mod) {
    if (typeCache[mod]) return typeCache[mod];
    typeCache[mod] = fetch(cfg.baseUrl + "/" + cfg.lang + "/types/" + mod + ".json")
      .then(function (r) { return r.ok ? r.json() : {}; })
      .catch(function () { return {}; });
    return typeCache[mod];
  }
  function initHover() {
    var popup = null;
    function hide() { if (popup) { popup.remove(); popup = null; } }
    document.querySelectorAll("a[data-type]").forEach(function (a) {
      a.addEventListener("mouseenter", function () {
        var spec = a.getAttribute("data-type").split("#");
        fetchTypes(spec[0]).then(function (tys) {
          var html = tys[spec[1]];
          if (!html) return;
          hide();
          popup = document.createElement("div");
          popup.className = "hover-popup";
          popup.innerHTML = html;
          document.body.appendChild(popup);
          var r = a.getBoundingClientRect();
          popup.style.left = (window.scrollX + r.left) + "px";
          popup.style.top = (window.scrollY + r.bottom + 4) + "px";
        });
      });
      a.addEventListener("mouseleave", hide);
    });
  }

  /* ---- same-definition occurrence highlight: hovering any identifier lights
          up every occurrence on the page that resolves to the same definition
          (code tokens, bound variables, and prose inline refs alike) -------- */
  function initOccur() {
    var groups = {};
    document.querySelectorAll("pre.Agda a[href], span.Agda a[href]").forEach(function (a) {
      var key = a.getAttribute("href");
      (groups[key] = groups[key] || []).push(a);
    });
    Object.keys(groups).forEach(function (key) {
      var as = groups[key];
      function set(on) {
        return function () {
          as.forEach(function (b) { b.classList.toggle("occ", on); });
        };
      }
      as.forEach(function (a) {
        a.addEventListener("mouseenter", set(true));
        a.addEventListener("mouseleave", set(false));
      });
    });
  }

  /* ---- search (fetch search.json once, simple fuzzy) ---------------------- */
  function fuzzy(q, s) {
    q = q.toLowerCase(); s = s.toLowerCase();
    if (s.indexOf(q) >= 0) return 100 - (s.length - q.length) * 0.1;
    var i = 0, score = 0;
    for (var j = 0; j < s.length && i < q.length; j++)
      if (s[j] === q[i]) { i++; score += 1; }
    return i === q.length ? score : -1;
  }
  function initSearch() {
    var box = document.getElementById("search-box");
    var out = document.getElementById("search-results");
    if (!box || !out) return;
    var data = null, sel = -1, shown = [];
    function load() {
      if (data) return Promise.resolve(data);
      return fetch(cfg.baseUrl + "/" + cfg.lang + "/search.json")
        .then(function (r) { return r.json(); })
        .then(function (d) { data = d; return d; }).catch(function () { return []; });
    }
    function render(q) {
      if (!q) { out.hidden = true; return; }
      shown = data.map(function (e) { return { e: e, s: fuzzy(q, e.name) }; })
        .filter(function (x) { return x.s >= 0; })
        .sort(function (a, b) { return b.s - a.s; }).slice(0, 25).map(function (x) { return x.e; });
      out.innerHTML = shown.map(function (e, i) {
        return '<a class="res' + (i === sel ? ' sel' : '') + '" href="' + e.href + '">' +
          '<span class="nm">' + esc(e.name) + '</span> ' +
          '<span class="mod">' + esc(e.module) + '</span>' +
          (e.type ? '<br><span class="ty">' + esc(e.type) + '</span>' : '') + '</a>';
      }).join("");
      out.hidden = shown.length === 0;
    }
    function esc(s) { var d = document.createElement("div"); d.textContent = s; return d.innerHTML; }
    box.addEventListener("input", function () { sel = -1; load().then(function () { render(box.value.trim()); }); });
    box.addEventListener("keydown", function (e) {
      if (out.hidden) return;
      if (e.key === "ArrowDown") { sel = Math.min(sel + 1, shown.length - 1); render(box.value.trim()); e.preventDefault(); }
      else if (e.key === "ArrowUp") { sel = Math.max(sel - 1, 0); render(box.value.trim()); e.preventDefault(); }
      else if (e.key === "Enter" && sel >= 0) { location.href = shown[sel].href; }
      else if (e.key === "Escape") { out.hidden = true; }
    });
    document.addEventListener("click", function (e) {
      if (!out.contains(e.target) && e.target !== box) out.hidden = true;
    });
  }
})();

/* The landing page keeps routes, the dependency map and the catalog in one place. */
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
      activate(panel ? panel.id : "reading-explorer", false, false);
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
