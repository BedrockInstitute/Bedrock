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
  function isDarkTheme() {
    if (root.classList.contains("theme-dark")) return true;
    if (root.classList.contains("theme-light")) return false;
    return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
  }
  applyTheme(storedTheme());
  document.addEventListener("DOMContentLoaded", function () {
    try { localStorage.setItem("bedrock-lang", cfg.lang); } catch (e) {}
    var btn = document.getElementById("theme-toggle");
    if (btn) btn.addEventListener("click", function () {
      var next = isDarkTheme() ? "light" : "dark";
      try { localStorage.setItem("bedrock-theme", next); } catch (_) {}
      applyTheme(next);
    });
    renderMath();
    initSearch();
    initHover();
    initOccur();
    initCodeNotes();
    initTermHover();
    initNav();
    initHeaderOffset();
    initSectionTracking();
  });

  /* Keep fragment targets below the complete sticky header. External Cubical pages add
     a banner above the topbar, and phone layouts may wrap the topbar onto a second row. */
  function initHeaderOffset() {
    var header = document.getElementById("site-header");
    if (!header) return;
    function measure() {
      document.documentElement.style.setProperty("--site-header-height", header.offsetHeight + "px");
      updateAnchorInset();
    }
    measure();
    if (window.ResizeObserver) new ResizeObserver(measure).observe(header);
    else window.addEventListener("resize", measure);
    /* On a reload Safari restores the reader's exact scroll offset itself. Re-running
       fragment navigation here would instead snap back to the section heading even
       when the document has not changed. Only correct the anchor on a fresh visit. */
    var navigation = performance.getEntriesByType && performance.getEntriesByType("navigation")[0];
    var isReload = navigation && navigation.type === "reload";
    if (location.hash && !isReload) {
      requestAnimationFrame(function () {
        measure();
        var target;
        try { target = document.getElementById(decodeURIComponent(location.hash.slice(1))); }
        catch (_) { target = null; }
        if (target) target.scrollIntoView({ block: "start" });
      });
    }
  }

  /* Fragment scrolling and section tracking must use the same resolved pixel
     inset. Safari can expose a computed calc(...) value here instead of pixels,
     so parsing scroll-padding-top itself is not reliable. */
  function updateAnchorInset() {
    var header = document.getElementById("site-header");
    var sectionBar = document.getElementById("section-sticky");
    var rootFontSize = parseFloat(getComputedStyle(document.documentElement).fontSize) || 16;
    var inset = (header ? header.offsetHeight : 0) + (sectionBar ? sectionBar.offsetHeight : 0) + rootFontSize;
    document.documentElement.style.setProperty("--anchor-inset", inset + "px");
    return inset;
  }

  /* Show the current heading hierarchy below the site header and keep the
     chapter contents in sync with the same scroll position. */
  function initSectionTracking() {
    if (document.body.classList.contains("learning-home")) return;
    var article = document.querySelector("article");
    if (!article) return;
    var chapterHeading = article.querySelector("h1[id]");
    var headings = Array.from(article.querySelectorAll("h2[id], h3[id], h4[id], h5[id], h6[id]"));
    if (!headings.length) return;

    var bar = document.createElement("nav");
    bar.id = "section-sticky";
    bar.setAttribute("aria-label", ({ en: "Current section", zh: "当前小节", ja: "現在の節" })[cfg.lang] || "Current section");
    document.body.appendChild(bar);
    document.documentElement.style.setProperty("--section-nav-height", "2.75rem");
    updateAnchorInset();

    var tocLinks = Array.from(document.querySelectorAll('#toc a[href*="#"]'));
    var scheduled = false;
    var lastActive = -2;

    function positionBar() {
      var rect = article.getBoundingClientRect();
      bar.style.setProperty("--section-nav-left", Math.max(0, rect.left) + "px");
      bar.style.setProperty("--section-nav-width", Math.min(rect.width, window.innerWidth - Math.max(0, rect.left)) + "px");
    }

    function render(activeIndex) {
      if (activeIndex === lastActive) return;
      lastActive = activeIndex;
      bar.replaceChildren();
      bar.classList.toggle("visible", activeIndex >= 0);

      var active = activeIndex >= 0 ? headings[activeIndex] : null;
      tocLinks.forEach(function (link) {
        if (active && link.hash === "#" + active.id) link.setAttribute("aria-current", "location");
        else link.removeAttribute("aria-current");
      });
      if (!active) return;

      var trail = [];
      if (chapterHeading) trail.push({ heading: chapterHeading, level: 1 });
      headings.slice(0, activeIndex + 1).forEach(function (heading) {
        var level = Number(heading.tagName.slice(1));
        while (trail.length && trail[trail.length - 1].level >= level) trail.pop();
        trail.push({ heading: heading, level: level });
      });
      trail.forEach(function (item, index) {
        if (index) {
          var separator = document.createElement("span");
          separator.className = "section-separator";
          separator.setAttribute("aria-hidden", "true");
          separator.textContent = "›";
          bar.appendChild(separator);
        }
        var link = document.createElement("a");
        link.href = "#" + item.heading.id;
        link.textContent = item.heading.textContent.trim();
        bar.appendChild(link);
      });
    }

    function update() {
      scheduled = false;
      positionBar();
      /* Fragment navigation and tracking share this resolved pixel inset. The
         extra pixel absorbs fractional layout rounding at an exact anchor. */
      var trackingLine = updateAnchorInset() + 1;
      var activeIndex = -1;
      headings.forEach(function (heading, index) {
        if (heading.getBoundingClientRect().top <= trackingLine) activeIndex = index;
      });
      /* Near the document end, the browser cannot always move the final heading
         as high as the tracking line. The final section is nevertheless active. */
      if (window.scrollY + window.innerHeight >= document.documentElement.scrollHeight - 2) {
        activeIndex = headings.length - 1;
      }
      render(activeIndex);
    }
    function schedule() {
      if (scheduled) return;
      scheduled = true;
      requestAnimationFrame(update);
    }

    update();
    window.addEventListener("scroll", schedule, { passive: true });
    window.addEventListener("resize", schedule);
    if (window.ResizeObserver) new ResizeObserver(schedule).observe(article);
  }

  /* ---- mobile navigation drawer ------------------------------------------- */
  function initNav() {
    var body = document.body;
    var toggle = document.getElementById("nav-toggle");
    var toc = document.getElementById("toc");
    if (!toggle || !toc) return;
    var backdrop = document.getElementById("nav-backdrop");
    var close = document.getElementById("nav-close");
    var fullLayout = window.matchMedia("(min-width: 95rem)");
    var collapse = document.createElement("button");
    collapse.id = "toc-collapse";
    collapse.type = "button";
    collapse.textContent = "‹";
    collapse.title = ({ en: "Collapse contents", zh: "收起目录", ja: "目次を閉じる" })[cfg.lang] || "Collapse contents";
    collapse.setAttribute("aria-label", collapse.title);
    toc.insertBefore(collapse, toc.firstChild);
    try {
      if (localStorage.getItem("bedrock-toc-collapsed") === "true") body.classList.add("nav-collapsed");
    } catch (_) {}
    function setCollapsed(collapsed) {
      if (body.classList.contains("nav-collapsed") === collapsed) return;
      var headerHeight = parseFloat(getComputedStyle(document.documentElement)
        .getPropertyValue("--site-header-height")) || 0;
      var sectionBar = document.getElementById("section-sticky");
      var readingY = headerHeight + (sectionBar && sectionBar.classList.contains("visible")
        ? sectionBar.offsetHeight : 0) + 18;
      var readingX = window.innerWidth / 2;
      var article = document.querySelector("article");
      var textRange = null;
      if (document.caretPositionFromPoint) {
        var caret = document.caretPositionFromPoint(readingX, readingY);
        if (caret) {
          textRange = document.createRange();
          textRange.setStart(caret.offsetNode, caret.offset);
          textRange.collapse(true);
        }
      } else if (document.caretRangeFromPoint) {
        textRange = document.caretRangeFromPoint(readingX, readingY);
      }
      if (textRange && article && !article.contains(textRange.startContainer)) textRange = null;
      var anchor = null;
      if (!textRange && article) {
        var blocks = Array.from(article.querySelectorAll("h1, h2, h3, h4, h5, h6, p, pre, ul, ol, .single-line-code"));
        var bestDistance = Infinity;
        blocks.forEach(function (block) {
          var rect = block.getBoundingClientRect();
          if (rect.bottom <= 0 || rect.top >= window.innerHeight) return;
          var distance = rect.top <= readingY && rect.bottom >= readingY
            ? 0 : Math.min(Math.abs(rect.top - readingY), Math.abs(rect.bottom - readingY));
          if (distance < bestDistance) { bestDistance = distance; anchor = block; }
        });
      }
      body.classList.add("nav-layout-changing");
      var marker = document.createElement("span");
      marker.className = "scroll-anchor-marker";
      marker.setAttribute("aria-hidden", "true");
      if (textRange) textRange.insertNode(marker);
      else if (anchor) anchor.insertBefore(marker, anchor.firstChild);
      else marker = null;
      var anchorTop = marker ? marker.getBoundingClientRect().top : null;
      body.classList.toggle("nav-collapsed", collapsed);
      try { localStorage.setItem("bedrock-toc-collapsed", collapsed ? "true" : "false"); } catch (_) {}
      requestAnimationFrame(function () {
        requestAnimationFrame(function () {
          var newTop = marker ? marker.getBoundingClientRect().top : null;
          if (newTop !== null && anchorTop !== null) window.scrollBy(0, newTop - anchorTop);
          if (marker) {
            var markerParent = marker.parentNode;
            marker.remove();
            if (markerParent) markerParent.normalize();
          }
          body.classList.remove("nav-layout-changing");
          window.dispatchEvent(new Event("resize"));
        });
      });
    }
    function setOpen(open, preserveScroll) {
      if (fullLayout.matches) {
        setCollapsed(!open);
        toggle.setAttribute("aria-expanded", open ? "true" : "false");
        return;
      }
      if (preserveScroll === undefined) preserveScroll = true;
      var savedX = window.scrollX;
      var savedY = window.scrollY;
      body.classList.toggle("nav-open", open);
      toggle.setAttribute("aria-expanded", open ? "true" : "false");
      if (backdrop) backdrop.hidden = !open;
      if (preserveScroll) {
        window.scrollTo(savedX, savedY);
        requestAnimationFrame(function () {
          window.scrollTo(savedX, savedY);
          requestAnimationFrame(function () { window.scrollTo(savedX, savedY); });
        });
      }
    }
    toggle.addEventListener("click", function () {
      setOpen(fullLayout.matches ? body.classList.contains("nav-collapsed")
                                 : !body.classList.contains("nav-open"));
    });
    collapse.addEventListener("click", function () { setCollapsed(true); });
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
      if (!fullLayout.matches && e.target.closest("a")) setOpen(false, false);
    });
    /* Leaving narrow layout (e.g. rotate to landscape) must not strand an open drawer. */
    (fullLayout.addEventListener ? fullLayout.addEventListener.bind(fullLayout, "change")
                                 : fullLayout.addListener.bind(fullLayout))(function (e) {
      body.classList.remove("nav-open");
      if (backdrop) backdrop.hidden = true;
      if (!e.matches) body.classList.remove("nav-collapsed");
      window.dispatchEvent(new Event("resize"));
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

  /* ---- responsive notes for reader-facing pseudo-code ------------------- */
  function collectProseNotes(article) {
    return Array.from(article.querySelectorAll(".prose-annotation-target")).map(function (target) {
      var template = target.nextElementSibling;
      if (!template || !template.classList.contains("prose-annotation-template")) return null;
      var note = document.createElement("aside");
      note.className = "prose-annotation-note";
      note.setAttribute("role", "note");
      note.appendChild(template.content.cloneNode(true));
      var connector = document.createElement("span");
      connector.className = "prose-annotation-connector";
      connector.setAttribute("aria-hidden", "true");
      article.appendChild(connector);
      article.appendChild(note);
      template.remove();
      return { target: target, note: note, connector: connector };
    }).filter(Boolean);
  }

  function positionMarginNotes(article, pairs) {
    var articleRect = article.getBoundingClientRect();
    pairs.forEach(function (pair) {
      var targetRect = pair.target.getBoundingClientRect();
      var y = targetRect.top - articleRect.top + targetRect.height / 2;
      pair.note.style.top = y + "px";
      pair.connector.style.top = y + "px";
      pair.note.style.setProperty("--note-width",
        Math.max(0, window.innerWidth - articleRect.right - 48) + "px");
    });
  }

  var SHOW_NOTE = ({ en: "Show note", zh: "显示注释", ja: "注釈を表示" })[cfg.lang] || "Show note";

  function initCodeNotes() {
    var article = document.querySelector("article");
    if (!article) return;
    var proseNotePairs = collectProseNotes(article);
    var notes = document.querySelectorAll(".single-line-code[data-note]");
    if (!notes.length && !proseNotePairs.length) return;
    function positionProseNotes() {
      positionMarginNotes(article, proseNotePairs);
      notes.forEach(function (block) {
        block.style.setProperty("--note-width",
          Math.max(0, window.innerWidth - block.getBoundingClientRect().right - 48) + "px");
      });
    }
    positionProseNotes();
    requestAnimationFrame(positionProseNotes);
    window.addEventListener("resize", positionProseNotes);
    if (window.ResizeObserver) {
      var proseNoteObserver = new ResizeObserver(positionProseNotes);
      proseNotePairs.forEach(function (pair) { proseNoteObserver.observe(pair.target); });
    }
    var toast = document.createElement("div");
    toast.id = "code-note-toast";
    toast.setAttribute("role", "dialog");
    toast.setAttribute("aria-label", ({ en: "Note", zh: "注释", ja: "注釈" })[cfg.lang] || "Note");
    var toastContent = document.createElement("div");
    toastContent.className = "code-note-content";
    var toastClose = document.createElement("button");
    toastClose.type = "button";
    toastClose.className = "code-note-close";
    toastClose.textContent = "×";
    toastClose.setAttribute("aria-label", ({ en: "Close note", zh: "关闭注释", ja: "注釈を閉じる" })[cfg.lang] || "Close note");
    toast.appendChild(toastContent);
    toast.appendChild(toastClose);
    toast.hidden = true;
    document.body.appendChild(toast);
    var activeTarget = null;
    var compactNotes = window.matchMedia("(max-width: 78.999rem)");
    function hide() {
      toast.hidden = true;
      toast.classList.remove("visible");
      if (activeTarget) activeTarget.setAttribute("aria-expanded", "false");
      activeTarget = null;
    }
    function positionToast() {
      if (!activeTarget || toast.hidden) return;
      var margin = 10;
      var gap = 12;
      var rootStyle = getComputedStyle(document.documentElement);
      var headerHeight = parseFloat(rootStyle.getPropertyValue("--site-header-height")) || 0;
      var sectionBar = document.getElementById("section-sticky");
      var topBoundary = headerHeight + (sectionBar && sectionBar.classList.contains("visible") ? sectionBar.offsetHeight : 0) + margin;
      var targetRect = activeTarget.getBoundingClientRect();
      toast.style.maxHeight = Math.max(6 * 16, window.innerHeight - topBoundary - margin) + "px";
      var toastRect = toast.getBoundingClientRect();
      var left = targetRect.left + targetRect.width / 2 - toastRect.width / 2;
      left = Math.max(margin, Math.min(left, window.innerWidth - toastRect.width - margin));
      var below = targetRect.bottom + gap;
      var above = targetRect.top - toastRect.height - gap;
      var useBelow = below + toastRect.height <= window.innerHeight - margin || above < topBoundary;
      var top = useBelow ? below : above;
      top = Math.max(topBoundary, Math.min(top, window.innerHeight - toastRect.height - margin));
      toast.style.left = left + "px";
      toast.style.top = top + "px";
      toast.dataset.side = useBelow ? "below" : "above";
      toast.style.setProperty("--note-arrow-x",
        Math.max(14, Math.min(targetRect.left + targetRect.width / 2 - left, toastRect.width - 14)) + "px");
    }
    function show(target, fill) {
      if (!compactNotes.matches) return;
      if (activeTarget === target && !toast.hidden) { hide(); return; }
      if (activeTarget) activeTarget.setAttribute("aria-expanded", "false");
      activeTarget = target;
      fill(toastContent);
      toast.hidden = false;
      toast.classList.add("visible");
      target.setAttribute("aria-expanded", "true");
      requestAnimationFrame(positionToast);
    }
    toastClose.addEventListener("click", hide);
    document.addEventListener("pointerdown", function (e) {
      if (!toast.hidden && !toast.contains(e.target) && e.target !== activeTarget) hide();
    });
    document.addEventListener("keydown", function (e) { if (e.key === "Escape") hide(); });
    window.addEventListener("resize", function () { if (!compactNotes.matches) hide(); else positionToast(); });
    window.addEventListener("scroll", positionToast, { passive: true });
    notes.forEach(function (el) {
      var target = el.querySelector("code");
      if (!target) return;
      var note = document.createElement("span");
      note.className = "single-line-code-note";
      note.textContent = el.getAttribute("data-note");
      note.setAttribute("role", "note");
      el.appendChild(note);
      target.setAttribute("tabindex", "0");
      target.setAttribute("role", "button");
      target.setAttribute("aria-label", SHOW_NOTE);
      target.setAttribute("aria-expanded", "false");
      target.addEventListener("click", function () {
        show(target, function (content) { content.textContent = el.getAttribute("data-note"); });
      });
      target.addEventListener("keydown", function (e) {
        if (e.key === "Enter" || e.key === " ") {
          e.preventDefault();
          show(target, function (content) { content.textContent = el.getAttribute("data-note"); });
        }
      });
    });
    proseNotePairs.forEach(function (pair) {
      var target = pair.target;
      var note = pair.note;
      function setActive(active) {
        target.classList.toggle("annotation-active", active);
        note.classList.toggle("annotation-active", active);
      }
      target.addEventListener("mouseenter", function () { setActive(true); });
      target.addEventListener("mouseleave", function () { setActive(false); });
      target.addEventListener("focus", function () { setActive(true); });
      target.addEventListener("blur", function () { setActive(false); });
      note.addEventListener("mouseenter", function () { setActive(true); });
      note.addEventListener("mouseleave", function () { setActive(false); });
      target.setAttribute("tabindex", "0");
      target.setAttribute("role", "button");
      target.setAttribute("aria-label", SHOW_NOTE);
      target.setAttribute("aria-expanded", "false");
      function showProseNote() {
        show(target, function (content) { content.innerHTML = note.innerHTML; });
      }
      target.addEventListener("click", showProseNote);
      target.addEventListener("keydown", function (e) {
        if (e.key === "Enter" || e.key === " ") { e.preventDefault(); showProseNote(); }
      });
    });
  }

  /* ---- reader-facing mathematical terms ---------------------------------- */
  function initTermHover() {
    var targets = document.querySelectorAll("[data-term]");
    if (!targets.length) return;
    var termsPromise = fetch(cfg.baseUrl + "/" + cfg.lang + "/terms.json")
      .then(function (response) { return response.ok ? response.json() : {}; })
      .catch(function () { return {}; });
    var popup = document.createElement("aside");
    popup.id = "term-popup";
    popup.setAttribute("role", "dialog");
    popup.hidden = true;
    document.body.appendChild(popup);
    var active = null;
    var closeTimer = null;
    var compact = window.matchMedia("(hover: none), (pointer: coarse)");
    var introLabel = ({ en: "First introduced in", zh: "首次引入于", ja: "最初の導入" })[cfg.lang] || "First introduced in";
    var introSeparator = cfg.lang === "en" ? ": " : "：";
    var closeLabel = ({ en: "Close term review", zh: "关闭术语回顾", ja: "用語の復習を閉じる" })[cfg.lang] || "Close term review";

    function cancelClose() {
      if (closeTimer) window.clearTimeout(closeTimer);
      closeTimer = null;
    }
    function hide() {
      cancelClose();
      popup.hidden = true;
      if (active) active.setAttribute("aria-expanded", "false");
      active = null;
    }
    function laterHide() {
      cancelClose();
      closeTimer = window.setTimeout(hide, 120);
    }
    function position() {
      if (!active || popup.hidden) return;
      var margin = 10;
      var gap = 9;
      var rect = active.getBoundingClientRect();
      var box = popup.getBoundingClientRect();
      var left = rect.left + rect.width / 2 - box.width / 2;
      left = Math.max(margin, Math.min(left, window.innerWidth - box.width - margin));
      var below = rect.bottom + gap;
      var above = rect.top - box.height - gap;
      var top = below + box.height <= window.innerHeight - margin ? below : above;
      top = Math.max(margin, Math.min(top, window.innerHeight - box.height - margin));
      popup.style.left = left + "px";
      popup.style.top = top + "px";
      popup.dataset.side = top >= rect.bottom ? "below" : "above";
      popup.style.setProperty("--term-arrow-x",
        Math.max(14, Math.min(rect.left + rect.width / 2 - left, box.width - 14)) + "px");
    }
    function show(target) {
      cancelClose();
      termsPromise.then(function (terms) {
        if (!target.isConnected) return;
        var term = terms[target.dataset.term];
        if (!term) return;
        if (active && active !== target) active.setAttribute("aria-expanded", "false");
        active = target;
        popup.replaceChildren();
        var name = document.createElement("strong");
        name.className = "term-popup-name";
        name.id = "term-popup-name";
        name.textContent = term.label;
        var recap = document.createElement("p");
        recap.id = "term-popup-recap";
        recap.textContent = term.recap;
        var link = document.createElement("a");
        link.href = term.href;
        link.textContent = introLabel + introSeparator + term.chapter;
        var close = document.createElement("button");
        close.className = "term-popup-close";
        close.type = "button";
        close.setAttribute("aria-label", closeLabel);
        close.textContent = "×";
        close.addEventListener("click", hide);
        popup.appendChild(name);
        popup.appendChild(recap);
        popup.appendChild(link);
        popup.appendChild(close);
        popup.setAttribute("aria-labelledby", "term-popup-name");
        popup.setAttribute("aria-describedby", "term-popup-recap");
        popup.hidden = false;
        target.setAttribute("aria-controls", "term-popup");
        target.setAttribute("aria-expanded", "true");
        requestAnimationFrame(position);
      });
    }

    targets.forEach(function (target) {
      target.setAttribute("aria-haspopup", "dialog");
      target.setAttribute("aria-expanded", "false");
      target.addEventListener("mouseenter", function () { show(target); });
      target.addEventListener("mouseleave", laterHide);
      target.addEventListener("focus", function () { show(target); });
      target.addEventListener("blur", laterHide);
      target.addEventListener("click", function (event) {
        if (target.tagName === "DFN" || compact.matches) {
          if (active === target && !popup.hidden && compact.matches) hide();
          else show(target);
          if (compact.matches) event.preventDefault();
        }
      });
    });
    popup.addEventListener("mouseenter", cancelClose);
    popup.addEventListener("mouseleave", laterHide);
    popup.addEventListener("focusin", cancelClose);
    popup.addEventListener("focusout", laterHide);
    document.addEventListener("pointerdown", function (event) {
      if (!popup.hidden && active && !popup.contains(event.target) && !active.contains(event.target)) hide();
    });
    document.addEventListener("keydown", function (event) { if (event.key === "Escape") hide(); });
    window.addEventListener("scroll", position, { passive: true });
    window.addEventListener("resize", position);
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
    var compactPointer = window.matchMedia("(hover: none), (pointer: coarse)");
    var definitionCopy = {
      en: "Go to definition",
      zh: "跳转到定义",
      ja: "定義へ移動"
    }[cfg.lang] || "Go to definition";
    function definitionAction(href) {
      var link = document.createElement("a");
      link.className = "type-definition-link";
      link.href = href;
      link.setAttribute("aria-label", definitionCopy);
      link.title = definitionCopy;
      link.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true">' +
        '<path d="M4 12h13m-5-5 5 5-5 5M20 5v14"/></svg>';
      return link;
    }
    var namePopup = null, nameAnchor = null, nameRequest = 0;
    function hideName() {
      nameRequest += 1;
      if (namePopup) namePopup.remove();
      namePopup = null; nameAnchor = null;
    }
    function positionName() {
      if (!namePopup || !nameAnchor) return;
      var rect = nameAnchor.getBoundingClientRect();
      var width = Math.min(namePopup.offsetWidth, window.innerWidth - 16);
      namePopup.style.left = (window.scrollX + Math.max(8,
        Math.min(rect.left, window.innerWidth - width - 8))) + "px";
      namePopup.style.top = (window.scrollY + rect.bottom) + "px";
    }
    function showName(name) {
      var serial = ++nameRequest;
      var spec = name.getAttribute("data-type").split("#");
      fetchTypes(spec[0]).then(function (types) {
        var html = types[spec[1]];
        if (serial !== nameRequest || !html || !name.isConnected) return;
        hideName();
        nameAnchor = name;
        namePopup = document.createElement("div");
        namePopup.className = "hover-popup name-hover-popup has-definition-link Agda";
        var nameValue = document.createElement("div");
        nameValue.className = "type-value Agda";
        nameValue.innerHTML = html;
        namePopup.appendChild(nameValue);
        namePopup.appendChild(definitionAction(name.href));
        document.body.appendChild(namePopup);
        namePopup.addEventListener("mouseleave", hideName);
        positionName();
      });
    }

    var popup = document.createElement("div");
    popup.className = "hover-popup type-inspector";
    popup.setAttribute("role", "dialog");
    popup.hidden = true;
    popup.innerHTML = '<div class="type-value Agda"></div>' +
      '<a class="type-definition-link" hidden></a>';
    document.body.appendChild(popup);
    var value = popup.querySelector(".type-value");
    var definitionLink = popup.querySelector(".type-definition-link");
    definitionLink.setAttribute("aria-label", definitionCopy);
    definitionLink.title = definitionCopy;
    definitionLink.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true">' +
      '<path d="M4 12h13m-5-5 5 5-5 5M20 5v14"/></svg>';
    var options = [], selected = null, anchor = null, renderedRequest = 0;
    var levelGesture = null;
    var rangeBlock = null, pinnedRangeBlock = null;
    var pinned = false;
    var request = 0;
    var rangeCopy = {
      en: { show: "Show ranges", hide: "Hide ranges" },
      zh: { show: "显示层级", hide: "隐藏层级" },
      ja: { show: "階層を表示", hide: "階層を隠す" }
    }[cfg.lang] || { show: "Show ranges", hide: "Hide ranges" };
    var rangeButtons = new Map();

    function updateRangeButton(block, active) {
      var button = rangeButtons.get(block);
      if (!button) return;
      var label = active ? rangeCopy.hide : rangeCopy.show;
      button.setAttribute("aria-pressed", String(active));
      button.setAttribute("aria-label", label);
      button.title = label;
      button.querySelector("span").textContent = label;
    }
    function setPinnedRangeBlock(block) {
      if (pinnedRangeBlock && pinnedRangeBlock !== block) {
        pinnedRangeBlock.classList.remove("ast-ranges-pinned");
        updateRangeButton(pinnedRangeBlock, false);
      }
      pinnedRangeBlock = block;
      if (block) {
        block.classList.add("ast-ranges-pinned");
        updateRangeButton(block, true);
      }
    }
    document.querySelectorAll("pre.Agda").forEach(function (block) {
      if (!block.querySelector(".expr-node")) return;
      var shell = document.createElement("div");
      shell.className = "agda-block-shell";
      block.parentNode.insertBefore(shell, block);
      shell.appendChild(block);
      var button = document.createElement("button");
      button.type = "button";
      button.className = "ast-range-toggle";
      button.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true">' +
        '<path d="M4 5.5h16v13H4zM8 9h8v6H8z"/></svg>' +
        '<span class="sr-only"></span>';
      shell.appendChild(button);
      rangeButtons.set(block, button);
      updateRangeButton(block, false);
      button.addEventListener("click", function (event) {
        event.preventDefault();
        event.stopPropagation();
        setPinnedRangeBlock(pinnedRangeBlock === block ? null : block);
      });
    });

    function expressionAncestors(target) {
      var node = target.closest && target.closest(".expr-node");
      var result = [];
      while (node) {
        result.push(node);
        node = node.parentElement && node.parentElement.closest(".expr-node");
      }
      return result;
    }
    function usesInspector(target) {
      /* Expression spans are emitted only inside Agda blocks, and only for
         applications. Inline/display Agda and a bare block identifier therefore
         keep the original name-type popup. */
      return expressionAncestors(target).length > 0;
    }
    function clearHighlight() {
      document.querySelectorAll(".expr-active, .name-active").forEach(function (node) {
        node.classList.remove("expr-active", "name-active");
      });
    }
    function position() {
      if (popup.hidden || !anchor) return;
      var rect = anchor.getBoundingClientRect();
      var width = Math.min(popup.offsetWidth, window.innerWidth - 16);
      var left = Math.max(8, Math.min(rect.left, window.innerWidth - width - 8));
      var below = rect.bottom;
      var desiredTop = below + popup.offsetHeight <= window.innerHeight - 8
        ? below : rect.top - popup.offsetHeight;
      var top = Math.max(8, Math.min(desiredTop,
        Math.max(8, window.innerHeight - popup.offsetHeight - 8)));
      popup.style.left = left + "px";
      popup.style.top = top + "px";
    }
    function vibrateSelection() {
      if (navigator.vibrate) navigator.vibrate(8);
    }
    function choose(index, withHapticFeedback) {
      if (!options.length) return;
      var option = options[Math.max(0, Math.min(index, options.length - 1))];
      var previous = selected;
      selected = option;
      if (withHapticFeedback && previous !== option) vibrateSelection();
      value.innerHTML = option.type;
      if (compactPointer.matches && option.href) {
        definitionLink.href = option.href;
        definitionLink.hidden = false;
        popup.classList.add("has-definition-link");
      } else {
        definitionLink.removeAttribute("href");
        definitionLink.hidden = true;
        popup.classList.remove("has-definition-link");
      }
      setPopupWidth(option);
      clearHighlight();
      document.querySelectorAll(".occ").forEach(function (node) {
        node.classList.remove("occ");
      });
      if (option.kind === "name" && option.nameNode)
        option.nameNode.classList.add("name-active");
      else if (option.node)
        option.node.classList.add("expr-active");
      requestAnimationFrame(position);
    }
    function gestureIndex(deltaX) {
      var distance = Math.abs(deltaX);
      if (distance < 12) return 0;
      return (deltaX < 0 ? -1 : 1) *
        (1 + Math.floor((distance - 12) / 28));
    }
    function applyLevelGesture() {
      if (!levelGesture || levelGesture.axis !== "horizontal" || !options.length
          || levelGesture.request !== request
          || levelGesture.request !== renderedRequest) return;
      if (levelGesture.baseIndex === null) {
        levelGesture.baseIndex = Math.max(0, options.indexOf(selected));
        levelGesture.lastIndex = levelGesture.baseIndex;
      }
      var next = Math.max(0, Math.min(options.length - 1,
        levelGesture.baseIndex + gestureIndex(levelGesture.deltaX)));
      if (next === levelGesture.lastIndex) return;
      levelGesture.lastIndex = next;
      choose(next, true);
      if (levelGesture && levelGesture.released) levelGesture = null;
    }
    function setPopupWidth(item) {
      var measure = document.createElement("div");
      measure.className = "hover-popup type-inspector type-inspector-measure";
      var sample = document.createElement("div");
      sample.className = "type-value Agda";
      sample.innerHTML = item.type;
      measure.appendChild(sample);
      if (compactPointer.matches && item.href) {
        measure.classList.add("has-definition-link");
        measure.appendChild(definitionAction(item.href));
      }
      document.body.appendChild(measure);
      popup.style.width = Math.ceil(measure.getBoundingClientRect().width) + "px";
      measure.remove();
    }
    function render(items, target, preferred) {
      options = items;
      anchor = target;
      var nextRangeBlock = target.closest && target.closest("pre.Agda");
      if (rangeBlock && rangeBlock !== nextRangeBlock)
        rangeBlock.classList.remove("ast-ranges-visible");
      if (pinnedRangeBlock && pinnedRangeBlock !== nextRangeBlock)
        setPinnedRangeBlock(null);
      rangeBlock = nextRangeBlock;
      if (rangeBlock) rangeBlock.classList.add("ast-ranges-visible");
      renderedRequest = request;
      popup.hidden = false;
      choose(Math.max(0, items.indexOf(preferred)));
      applyLevelGesture();
    }
    function show(target) {
      hideName();
      var serial = ++request;
      var spans = expressionAncestors(target);
      var name = target.closest && target.closest("a[data-type]");
      var directNode = name ? null
        : target.closest && target.closest(".expr-node");
      var pageRequest = spans.length ? fetchTypes(cfg.chapter || cfg.module) : Promise.resolve({});
      var nameSpec = name ? name.getAttribute("data-type").split("#") : null;
      var nameRequest = nameSpec ? fetchTypes(nameSpec[0]) : Promise.resolve({});
      Promise.all([pageRequest, nameRequest]).then(function (loaded) {
        if (serial !== request || !target.isConnected) return;
        var expressionData = loaded[0].$expressions || {};
        var items = spans.map(function (node) {
          var data = expressionData[node.dataset.exprId];
          return data && { kind: "expression", node: node, source: data.source,
                           type: data.type, start: data.start, end: data.end,
                           astKind: data.kind };
        }).filter(Boolean);
        if (nameSpec && loaded[1][nameSpec[1]]) {
          var canonicalName = name.getAttribute("data-name") ||
            (loaded[1].$names || {})[nameSpec[1]];
          /* The pointer is directly over this identifier, so its name type is
             preferred. Width follows the displayed type: reserving space for
             every enclosing application leaves short variable types in a large,
             mostly empty popup now that node selection happens in the source. */
          items.unshift({ kind: "name", node: null, nameNode: name,
                          source: canonicalName || name.textContent.trim(),
                          type: loaded[1][nameSpec[1]], href: name.href,
                          start: Number(name.id),
                          end: Number(name.id) + Array.from(name.textContent).length });
        }
        items.sort(function (left, right) {
          if (left.kind === "name") return right.kind === "name" ? 0 : -1;
          if (right.kind === "name") return 1;
          var leftWidth = left.end - left.start;
          var rightWidth = right.end - right.start;
          return leftWidth - rightWidth || right.start - left.start;
        });
        var preferred = name
          ? items.find(function (item) { return item.kind === "name"; })
          : items.find(function (item) { return item.node === directNode; });
        if (items.length) render(items, name || directNode || target,
                                 preferred || items[0]);
      });
    }
    function hide() {
      if (pinned) return;
      request += 1;
      popup.hidden = true; options = []; selected = null; anchor = null; clearHighlight();
      if (rangeBlock) rangeBlock.classList.remove("ast-ranges-visible");
      rangeBlock = null;
    }
    function laterHide() {
      if (compactPointer.matches) return;
      hide();
    }

    document.addEventListener("mouseover", function (event) {
      if (compactPointer.matches) return;
      if (!usesInspector(event.target)) return;
      var target = event.target.closest && event.target.closest(".expr-node, a[data-type]");
      if (!target || popup.contains(target)) return;
      var hovered = event.target;
      if (!hovered.isConnected || !hovered.matches(":hover")) return;
      pinned = false; show(hovered);
    });
    document.addEventListener("mouseout", function (event) {
      if (compactPointer.matches) return;
      if (!usesInspector(event.target)) return;
      var target = event.target.closest && event.target.closest(".expr-node, a[data-type]");
      var currentRoots = expressionAncestors(event.target);
      var relatedRoots = event.relatedTarget ? expressionAncestors(event.relatedTarget) : [];
      var currentRoot = currentRoots[currentRoots.length - 1];
      var relatedRoot = relatedRoots[relatedRoots.length - 1];
      if (currentRoot && currentRoot === relatedRoot) return;
      if (target && (!event.relatedTarget || (!target.contains(event.relatedTarget)
          && !popup.contains(event.relatedTarget)))) laterHide();
    });
    document.addEventListener("click", function (event) {
      if (compactPointer.matches) {
        var touched = event.target.closest && event.target.closest("a[data-type], .expr-node");
        if (touched) {
          event.preventDefault();
          event.stopPropagation();
          return;
        }
      }
      if (!usesInspector(event.target)) return;
      var node = event.target.closest && event.target.closest(".expr-node");
      if (!node || popup.contains(event.target)) return;
      pinned = true;
      show(event.target);
    });
    popup.addEventListener("mouseleave", laterHide);
    document.addEventListener("pointerdown", function (event) {
      if (!compactPointer.matches) {
        if (!popup.hidden && !popup.contains(event.target)
            && !(event.target.closest && event.target.closest(".expr-node, a[data-type]"))) {
          pinned = false; hide();
        }
        return;
      }
      var codeBlock = event.target.closest && event.target.closest("pre.Agda");
      var target = event.target.closest && event.target.closest("a[data-type], .expr-node");
      if (codeBlock && !target) {
        pinned = false;
        hide(); hideName();
        return;
      }
      if ((popup.contains(event.target) || (namePopup && namePopup.contains(event.target)))
          && !(target && target.matches("a[data-type]"))) return;
      if (!target) {
        pinned = false; hide(); hideName();
        return;
      }
      if (usesInspector(event.target)) {
        vibrateSelection();
        hideName(); pinned = true; show(event.target);
      } else if (target.matches("a[data-type]")) {
        levelGesture = null;
        pinned = false;
        if (!popup.hidden) hide();
        showName(target);
      }
    });
    document.addEventListener("touchstart", function (event) {
      if (!compactPointer.matches || event.touches.length !== 1
          || !usesInspector(event.target)) return;
      var touch = event.touches[0];
      levelGesture = {
        target: event.target,
        block: event.target.closest && event.target.closest("pre.Agda"),
        request: request,
        startX: touch.clientX,
        startY: touch.clientY,
        deltaX: 0,
        axis: null,
        baseIndex: null,
        lastIndex: null
      };
    });
    document.addEventListener("selectstart", function (event) {
      if (!compactPointer.matches) return;
      var expression = event.target.closest && event.target.closest(".expr-node");
      if (expression) event.preventDefault();
    });
    document.addEventListener("touchmove", function (event) {
      if (!compactPointer.matches || !levelGesture || event.touches.length !== 1) return;
      var touch = event.touches[0];
      var deltaX = touch.clientX - levelGesture.startX;
      var deltaY = touch.clientY - levelGesture.startY;
      if (!levelGesture.axis) {
        if (Math.abs(deltaY) >= 10 && Math.abs(deltaY) > Math.abs(deltaX)) {
          levelGesture.axis = "vertical";
          return;
        }
        if (Math.abs(deltaX) < 12 || Math.abs(deltaX) <= Math.abs(deltaY) * 1.15)
          return;
        levelGesture.axis = "horizontal";
        if (levelGesture.block) levelGesture.block.classList.add("ast-level-gesture");
      }
      if (levelGesture.axis !== "horizontal") return;
      levelGesture.deltaX = deltaX;
      applyLevelGesture();
    });
    function finishLevelGesture(event) {
      if (!levelGesture) return;
      if (levelGesture.block) levelGesture.block.classList.remove("ast-level-gesture");
      if (event.type === "touchcancel" || levelGesture.axis !== "horizontal"
          || levelGesture.request === renderedRequest) levelGesture = null;
      else levelGesture.released = true;
    }
    document.addEventListener("touchend", finishLevelGesture);
    document.addEventListener("touchcancel", finishLevelGesture);
    document.addEventListener("keydown", function (event) {
      if (event.key === "Escape") { pinned = false; hide(); hideName(); }
    });
    document.addEventListener("mouseover", function (event) {
      if (compactPointer.matches) return;
      var name = event.target.closest && event.target.closest("a[data-type]");
      if (!name || usesInspector(event.target)
          || (event.relatedTarget && name.contains(event.relatedTarget))) return;
      /* A type rendered inside the inspector can itself be inspected. */
      if (!popup.contains(name)) {
        pinned = false;
        if (!popup.hidden) hide();
      }
      if (!name.isConnected || !name.matches(":hover")) return;
      showName(name);
    });
    document.addEventListener("mouseout", function (event) {
      if (compactPointer.matches) return;
      var name = event.target.closest && event.target.closest("a[data-type]");
      if (name && !usesInspector(event.target)
          && (!event.relatedTarget || (!name.contains(event.relatedTarget)
              && !(namePopup && namePopup.contains(event.relatedTarget))))) hideName();
    });
    window.addEventListener("scroll", function () { position(); positionName(); }, { passive: true });
    window.addEventListener("resize", function () {
      if (!popup.hidden && selected) setPopupWidth(selected);
      position(); positionName();
    });
  }

  /* ---- same-definition occurrence highlight: hovering any identifier lights
          up every occurrence on the page that resolves to the same definition
          (code tokens, bound variables, and prose inline refs alike) -------- */
  function initOccur() {
    function occurrenceKey(link) {
      /* Resolve relative links before comparing them. A note is cloned into a
         body-level popover, while its matching occurrence can live in prose or
         generated Agda; the resolved definition URL is their shared identity. */
      try { return new URL(link.getAttribute("href"), document.baseURI).href; }
      catch (_) { return link.getAttribute("href"); }
    }
    function occurrenceLink(target) {
      return target.closest && target.closest("pre.Agda a[href], span.Agda a[href]");
    }
    function set(key, on) {
      document.querySelectorAll("pre.Agda a[href], span.Agda a[href]").forEach(function (link) {
        if (occurrenceKey(link) === key) link.classList.toggle("occ", on);
      });
    }
    document.addEventListener("mouseover", function (event) {
      var link = occurrenceLink(event.target);
      if (!link || (event.relatedTarget && link.contains(event.relatedTarget))) return;
      set(occurrenceKey(link), true);
    });
    document.addEventListener("mouseout", function (event) {
      var link = occurrenceLink(event.target);
      if (!link || (event.relatedTarget && link.contains(event.relatedTarget))) return;
      set(occurrenceKey(link), false);
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
