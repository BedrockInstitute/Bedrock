/* Bedrock site behaviour: theme toggle, KaTeX rendering, type-on-hover, search.
 *
 * The type-on-hover mechanism is modelled on the 1lab's highlight-hover (AGPL-3.0,
 * https://1lab.dev) but reimplemented for Bedrock's `types/<Module>.json` sidecars.
 * Vanilla JS, no build step. See NOTICE.
 */
(function () {
  "use strict";
  var cfg = window.bedrock || { baseUrl: "", lang: "en", module: "" };
  var compactPointer = window.matchMedia("(hover: none), (pointer: coarse)");
  var isDefinitionModalDocument =
    new URLSearchParams(location.search).get("bedrock-modal") === "1";
  if (isDefinitionModalDocument)
    document.documentElement.classList.add("definition-modal-document");
  function modalReadingScroller() {
    return isDefinitionModalDocument ? document.getElementById("main-content") : null;
  }

  /* A compact-pointer definition follows one shared two-step interaction in
     source code, hover popups, and modal documents: the definition occurrence
     opens its hover first, and only the hover's explicit action opens a modal. */
  function definitionHoverTarget(target) {
    var candidate = target && target.closest && target.closest(
      "a[data-type], .type-node[data-expression-type], .expr-node, .Agda a[href]"
    );
    return candidate && !candidate.classList.contains("type-definition-link")
      ? candidate : null;
  }
  function isDefinitionPopupAction(link) {
    return Boolean(link && link.classList.contains("type-definition-link"));
  }
  function isUniverseTypeText(text) {
    var normalized = (text || "").replace(/\s+/g, " ").trim();
    if (/^Type(?:ω|[₀-₉]+)?$/.test(normalized)) return true;
    if (normalized.indexOf("Type ") !== 0) return false;
    /* A universe level may contain names, successors, joins and parentheses,
       but a function, binder or product whose first token is Type is not itself
       a universe and must remain inspectable. */
    return !/[→,:{}\[\]=≃×]/.test(normalized.slice(5));
  }
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
    initDefinitionModals();
    initOccur();
    initCodeNotes();
    initTermHover();
    initSubmoduleFolds();
    initNav();
    initPageScroll();
    initHeaderOffset();
    initSectionTracking();
    initMobileSearchScroll();
    initCurrentRoute();
  });

  /* Keep the Agda module declaration visible while its body folds as one unit. */
  function initSubmoduleFolds() {
    document.querySelectorAll("details.submodule-fold").forEach(function (details) {
      var heading = details.querySelector(":scope > summary.submodule-fold-heading");
      var content = details.querySelector(":scope > .submodule-fold-content");
      if (!heading || !content) return;
      var expanded = details.open;
      var animation = null;
      heading.addEventListener("click", function (event) {
        if (event.target.closest("a")) {
          event.stopPropagation();
          return;
        }
        if (!content.animate || window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
          expanded = !details.open;
          return;
        }
        event.preventDefault();
        var startHeight = details.open ? content.getBoundingClientRect().height : 0;
        var startOpacity = details.open ? parseFloat(getComputedStyle(content).opacity) : 0;
        if (animation) animation.cancel();
        expanded = !expanded;
        details.open = true;
        content.style.height = startHeight + "px";
        content.style.overflow = "hidden";
        details.classList.toggle("submodule-closing", !expanded);
        var endHeight = expanded ? content.scrollHeight : 0;
        var motion = content.animate([
          { height: startHeight + "px", opacity: startOpacity },
          { height: endHeight + "px", opacity: expanded ? 1 : 0 }
        ], { duration: 260, easing: "cubic-bezier(.2,.75,.25,1)", fill: "forwards" });
        animation = motion;
        motion.onfinish = function () {
          if (animation !== motion) return;
          details.open = expanded;
          motion.cancel();
          animation = null;
          content.style.height = "";
          content.style.overflow = "";
          details.classList.remove("submodule-closing");
        };
      });
    });
  }

  /* Page-edge controls are shared by chapters, the reading guide and library pages. */
  function initPageScroll() {
    var labels = ({
      en: ["Page scrolling", "Scroll to top", "Scroll to bottom"],
      zh: ["页面滚动", "回到顶部", "直达底部"],
      ja: ["ページ移動", "ページの先頭へ", "ページの末尾へ"]
    })[cfg.lang] || ["Page scrolling", "Scroll to top", "Scroll to bottom"];
    var controls = document.createElement("nav");
    controls.className = "page-scroll";
    controls.setAttribute("aria-label", labels[0]);
    ["top", "bottom"].forEach(function (edge, i) {
      var button = document.createElement("button");
      button.type = "button";
      button.title = labels[i + 1];
      button.setAttribute("aria-label", labels[i + 1]);
      button.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true" focusable="false">' +
        '<path d="' + (edge === "top" ? "M5 4h14M6 13l6-6 6 6M12 7v13" :
          "M5 20h14M6 11l6 6 6-6M12 17V4") + '"/></svg>';
      button.addEventListener("click", function () {
        var scroller = modalReadingScroller();
        if (scroller) scroller.scrollTo({ top: edge === "top" ? 0 : scroller.scrollHeight,
          behavior: "smooth" });
        else window.scrollTo({ top: edge === "top" ? 0 : document.documentElement.scrollHeight,
          behavior: "smooth" });
      });
      controls.appendChild(button);
    });
    document.body.appendChild(controls);
  }

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
    /* The parent modal aligns the whole Agda block. Re-running ordinary page
       fragment navigation here would align the identifier inside that block
       and overwrite the parent's result one frame later. */
    if (location.hash && !isReload && !isDefinitionModalDocument) {
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

  /* On narrow phones, the search row gives its space back while reading down. */
  function initMobileSearchScroll() {
    var form = document.querySelector("#topbar .search-form");
    if (!form || !window.matchMedia) return;
    var mobile = window.matchMedia("(max-width: 28rem)");
    var anchorY = window.scrollY;
    var settling = false;
    function setHidden(hidden) {
      hidden = hidden && mobile.matches && !form.contains(document.activeElement);
      if (document.body.classList.contains("mobile-search-hidden") === hidden) return;
      document.body.classList.toggle("mobile-search-hidden", hidden);
      settling = true;
      requestAnimationFrame(function () {
        anchorY = window.scrollY;
        settling = false;
      });
    }
    window.addEventListener("scroll", function () {
      var y = window.scrollY;
      if (settling) { anchorY = y; return; }
      if (!mobile.matches || y <= 8) setHidden(false);
      else if (Math.abs(y - anchorY) >= 8) setHidden(y > anchorY);
      if (Math.abs(y - anchorY) >= 8) anchorY = y;
    }, { passive: true });
    form.addEventListener("focusin", function () { setHidden(false); });
    (mobile.addEventListener ? mobile.addEventListener.bind(mobile, "change")
                             : mobile.addListener.bind(mobile))(function () {
      setHidden(false);
      anchorY = window.scrollY;
    });
  }

  /* The sidebar follows the route last chosen in the guide when that route
     contains the current chapter; otherwise it shows the chapter's first route. */
  function initCurrentRoute() {
    var section = document.querySelector("#toc .current-route");
    if (!section) return;
    var list = section.querySelector(".route-nav");
    var name = section.querySelector(".current-route-name");
    var current = section.dataset.current;
    var data = null;
    function showRoute() {
      if (!data) return;
      var preferred = "";
      try { preferred = localStorage.getItem("bedrock-current-route-v1") || ""; } catch (_) {}
      var route = data.routes.find(function (item) {
        return item.id === preferred && (!current || item.chapters.includes(current));
      }) || data.routes.find(function (item) { return item.chapters.includes(current); })
        || data.routes[0];
      if (!route) return;
      var nodes = new Map(data.nodes.map(function (node) { return [node.id, node]; }));
      name.textContent = route.title[cfg.lang] || route.title.en;
      list.dataset.route = route.id;
      list.replaceChildren();
      route.chapters.forEach(function (id) {
        var node = nodes.get(id);
        if (!node) return;
        var item = document.createElement("li");
        var link = document.createElement("a");
        link.href = node.page + node.anchor;
        link.dataset.chapter = id;
        link.textContent = node.title[cfg.lang] || node.title.en;
        if (id === current) link.setAttribute("aria-current", "page");
        item.appendChild(link);
        list.appendChild(item);
      });
    }
    window.addEventListener("bedrock:current-route", showRoute);
    fetch(cfg.baseUrl + "/" + cfg.lang + "/reading-routes.json")
      .then(function (response) { if (!response.ok) throw new Error(response.status); return response.json(); })
      .then(function (loaded) { data = loaded; showRoute(); })
      .catch(function () { /* The server-rendered route remains usable. */ });
  }

  function sectionOutline(headings) {
    var roots = [], stack = [];
    headings.forEach(function (heading) {
      var level = Number(heading.tagName.slice(1));
      var node = { heading: heading, level: level, children: [] };
      while (stack.length && stack[stack.length - 1].level >= level) stack.pop();
      (stack.length ? stack[stack.length - 1].children : roots).push(node);
      stack.push(node);
    });
    return roots;
  }

  /* The sticky breadcrumb doubles as a compact, complete chapter directory. */
  function initSectionTracking() {
    if (document.body.classList.contains("learning-home")) return;
    var article = document.querySelector("article");
    if (!article) return;
    var chapterHeading = article.querySelector("h1[id]");
    var headings = Array.from(article.querySelectorAll("h2[id], h3[id], h4[id], h5[id], h6[id]"));
    if (!headings.length) return;

    var labels = ({
      en: { contents: "Chapter contents", expand: "Expand", collapse: "Collapse" },
      zh: { contents: "本章目录", expand: "展开", collapse: "折叠" },
      ja: { contents: "この章の目次", expand: "展開", collapse: "折りたたむ" }
    })[cfg.lang] || { contents: "Chapter contents", expand: "Expand", collapse: "Collapse" };
    var bar = document.createElement("div");
    bar.id = "section-sticky";
    bar.className = "visible";
    var trigger = document.createElement("button");
    trigger.type = "button";
    trigger.className = "section-trigger";
    trigger.setAttribute("aria-expanded", "false");
    trigger.setAttribute("aria-controls", "section-menu");
    var trailText = document.createElement("span");
    trailText.className = "section-trail";
    var chevron = document.createElement("span");
    chevron.className = "section-chevron";
    chevron.setAttribute("aria-hidden", "true");
    trigger.append(trailText, chevron);
    var panel = document.createElement("nav");
    panel.id = "section-menu";
    panel.setAttribute("aria-label", labels.contents);
    panel.hidden = true;
    var menuList = document.createElement("ul");
    menuList.className = "section-menu-list";
    panel.appendChild(menuList);
    bar.append(trigger, panel);
    article.insertBefore(bar, article.firstChild);
    document.documentElement.style.setProperty("--section-nav-height", "2.75rem");
    updateAnchorInset();

    var tocLinks = Array.from(document.querySelectorAll('#toc a[href*="#"]'));
    var tocBranches = Array.from(document.querySelectorAll("#toc .toc-branch"));
    var menuLinks = [];
    var menuBranches = [];
    var activeHeading = null;
    var scheduled = false;
    var lastActive = -2;

    function menuLink(heading) {
      var link = document.createElement("a");
      link.href = "#" + heading.id;
      link.textContent = heading.textContent.trim();
      menuLinks.push(link);
      return link;
    }

    function addMenuNodes(nodes, parent) {
      nodes.forEach(function (node) {
        var item = document.createElement("li");
        item.className = "section-menu-item";
        var row = document.createElement("div");
        row.className = "section-menu-row";
        row.appendChild(menuLink(node.heading));
        item.appendChild(row);
        if (node.children.length) {
          row.classList.add("has-children");
          var children = document.createElement("ul");
          children.id = "section-menu-children-" + node.heading.id;
          children.hidden = true;
          var toggle = document.createElement("button");
          toggle.type = "button";
          toggle.className = "section-branch-toggle";
          toggle.setAttribute("aria-expanded", "false");
          toggle.setAttribute("aria-controls", children.id);
          function setBranchOpen(open) {
            children.hidden = !open;
            toggle.setAttribute("aria-expanded", open ? "true" : "false");
            toggle.setAttribute("aria-label", (open ? labels.collapse : labels.expand)
                                + " " + node.heading.textContent.trim());
          }
          setBranchOpen(false);
          toggle.addEventListener("click", function () {
            setBranchOpen(children.hidden);
          });
          row.addEventListener("click", function (event) {
            if (event.target === row) setBranchOpen(children.hidden);
          });
          row.appendChild(toggle);
          addMenuNodes(node.children, children);
          item.appendChild(children);
          menuBranches.push({ node: node, setOpen: setBranchOpen });
        }
        parent.appendChild(item);
      });
    }

    addMenuNodes(sectionOutline(headings), menuList);

    function containsHeading(node, heading) {
      return node.heading === heading || node.children.some(function (child) {
        return containsHeading(child, heading);
      });
    }

    function setMenuOpen(open, restoreFocus) {
      if (panel.hidden === !open) return;
      if (open) {
        document.dispatchEvent(new Event("bedrock:section-menu-open"));
        menuBranches.forEach(function (branch) {
          branch.setOpen(!!activeHeading && containsHeading(branch.node, activeHeading));
        });
        panel.scrollTop = 0;
      }
      panel.hidden = !open;
      bar.classList.toggle("menu-open", open);
      trigger.setAttribute("aria-expanded", open ? "true" : "false");
      if (!open && restoreFocus) trigger.focus();
    }

    trigger.addEventListener("click", function () { setMenuOpen(panel.hidden); });
    panel.addEventListener("click", function (event) {
      var link = event.target.closest("a[href^='#']");
      if (!link) return;
      var sameTarget = link.hash === window.location.hash;
      setMenuOpen(false);
      if (sameTarget) requestAnimationFrame(function () {
        document.getElementById(link.hash.slice(1)).scrollIntoView({ block: "start" });
      });
    });
    document.addEventListener("pointerdown", function (event) {
      if (!panel.hidden && !bar.contains(event.target)) setMenuOpen(false);
    });
    document.addEventListener("keydown", function (event) {
      if (event.key === "Escape" && !panel.hidden) setMenuOpen(false, true);
    });
    document.addEventListener("bedrock:sidebar-open", function () {
      if (!panel.hidden) setMenuOpen(false);
    });

    function revealTocLink(link) {
      var toc = document.getElementById("toc");
      if (!toc || !link) return;
      var tocRect = toc.getBoundingClientRect();
      var linkRect = link.getBoundingClientRect();
      var margin = 8;
      if (linkRect.top < tocRect.top + margin) {
        toc.scrollTop += linkRect.top - tocRect.top - margin;
      } else if (linkRect.bottom > tocRect.bottom - margin) {
        toc.scrollTop += linkRect.bottom - tocRect.bottom + margin;
      }
    }

    function syncTocBranches(activeLink) {
      tocBranches.forEach(function (branch) {
        branch.open = !!activeLink && branch.contains(activeLink);
      });
    }

    function render(activeIndex) {
      if (activeIndex === lastActive) return;
      lastActive = activeIndex;
      var active = activeIndex >= 0 ? headings[activeIndex] : null;
      activeHeading = active;
      var currentId = (active || chapterHeading || {}).id;
      menuLinks.forEach(function (link) {
        if (link.hash === "#" + currentId) link.setAttribute("aria-current", "location");
        else link.removeAttribute("aria-current");
      });
      var activeTocLink = null;
      tocLinks.forEach(function (link) {
        if (active && link.hash === "#" + active.id) {
          link.setAttribute("aria-current", "location");
          activeTocLink = link;
        } else link.removeAttribute("aria-current");
      });
      // Sync only when the reading section changes, so manual toggles remain usable.
      syncTocBranches(activeTocLink);
      revealTocLink(activeTocLink);
      var trail = [];
      if (chapterHeading) trail.push({ heading: chapterHeading, level: 1 });
      headings.slice(0, activeIndex + 1).forEach(function (heading) {
        var level = Number(heading.tagName.slice(1));
        while (trail.length && trail[trail.length - 1].level >= level) trail.pop();
        trail.push({ heading: heading, level: level });
      });
      trailText.replaceChildren();
      trail.forEach(function (item, index) {
        if (index) {
          var separator = document.createElement("span");
          separator.className = "section-separator";
          separator.setAttribute("aria-hidden", "true");
          separator.textContent = "›";
          trailText.appendChild(separator);
        }
        var crumb = document.createElement("span");
        crumb.textContent = item.heading.textContent.trim();
        trailText.appendChild(crumb);
      });
      trigger.setAttribute("aria-label", labels.contents + "：" + trail.map(function (item) {
        return item.heading.textContent.trim();
      }).join(" › "));
    }

    function update() {
      scheduled = false;
      /* Fragment navigation and tracking share this resolved pixel inset. The
         extra pixel absorbs fractional layout rounding at an exact anchor. */
      var scroller = modalReadingScroller();
      var trackingLine = scroller
        ? scroller.getBoundingClientRect().top + bar.offsetHeight + 1
        : updateAnchorInset() + 1;
      var activeIndex = -1;
      headings.forEach(function (heading, index) {
        if (heading.getBoundingClientRect().top <= trackingLine) activeIndex = index;
      });
      /* Near the document end, the browser cannot always move the final heading
         as high as the tracking line. The final section is nevertheless active. */
      if (scroller ? scroller.scrollTop + scroller.clientHeight >= scroller.scrollHeight - 2
          : window.scrollY + window.innerHeight >= document.documentElement.scrollHeight - 2) {
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
    (modalReadingScroller() || window).addEventListener("scroll", function () {
      if (!panel.hidden) setMenuOpen(false);
      schedule();
    }, { passive: true });
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
    var menuLabel = toggle.getAttribute("aria-label");
    var closeLabel = close ? close.getAttribute("aria-label") : menuLabel;
    function setToggleState(open) {
      toggle.setAttribute("aria-expanded", open ? "true" : "false");
      toggle.setAttribute("aria-label", open ? closeLabel : menuLabel);
      toggle.title = open ? closeLabel : menuLabel;
    }
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
    setToggleState(fullLayout.matches && !body.classList.contains("nav-collapsed"));
    function setCollapsed(collapsed) {
      setToggleState(!collapsed);
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
      if (open) document.dispatchEvent(new Event("bedrock:sidebar-open"));
      if (fullLayout.matches) {
        setCollapsed(!open);
        return;
      }
      if (preserveScroll === undefined) preserveScroll = true;
      var savedX = window.scrollX;
      var savedY = window.scrollY;
      body.classList.toggle("nav-open", open);
      setToggleState(open);
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
    document.addEventListener("bedrock:section-menu-open", function () {
      if (body.classList.contains("nav-open")) setOpen(false);
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
      setToggleState(e.matches && !body.classList.contains("nav-collapsed"));
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
        name.textContent = term.abbreviation
          ? term.label + " (" + term.abbreviation + ")" : term.label;
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
    var definitionCopy = {
      en: "Open definition in a modal",
      zh: "在弹窗中打开定义",
      ja: "モーダルで定義を開く"
    }[cfg.lang] || "Open definition in a modal";
    var definitionActionIcon = '<svg viewBox="0 0 24 24" aria-hidden="true">' +
      '<rect x="3" y="4" width="18" height="16" rx="2"/>' +
      '<path d="M3 8h18"/><rect x="7" y="11" width="10" height="6" rx="1"/>' +
      '</svg>';
    var swipeHintCopy = {
      en: "Hold a highlighted range and swipe sideways to switch AST nodes",
      zh: "按住色块左右滑动以切换AST节点",
      ja: "色付き範囲を長押しして左右にスワイプするとASTノードを切り替えられます"
    }[cfg.lang] || "Hold a highlighted range and swipe sideways to switch AST nodes";
    function definitionAction(href, name) {
      var link = document.createElement("a");
      link.className = "type-definition-link";
      link.href = href;
      if (name) link.setAttribute("data-name", name);
      link.setAttribute("aria-label", definitionCopy);
      link.title = definitionCopy;
      link.innerHTML = definitionActionIcon;
      return link;
    }
    function escapedCodeName(name) {
      var span = document.createElement("span");
      span.textContent = name;
      return span.innerHTML;
    }
    var hoverCloseDelay = 360;
    function scheduleHoverClose(callback) {
      if (compactPointer.matches) return null;
      return window.setTimeout(function () {
        /* A viewport can become compact while a desktop timer is pending, for
           example when a phone rotates or responsive preview mode changes. */
        if (!compactPointer.matches) callback();
      }, hoverCloseDelay);
    }
    var namePopups = [], nameRequest = 0;
    var leafActiveName = null;
    function clearLeafNameHighlight() {
      if (leafActiveName) leafActiveName.classList.remove("name-active");
      leafActiveName = null;
    }
    function hoverIdentity(name) {
      return name && name.getAttribute && (
        name.getAttribute("data-expression-type") || name.getAttribute("data-type")
      );
    }
    function markTerminalHoverStops(value, identity) {
      if (!value) return;
      if (identity) {
        value.querySelectorAll("[data-type], [data-expression-type]").forEach(function (node) {
          if (hoverIdentity(node) === identity
              && !node.hasAttribute("data-hover-stop"))
            node.setAttribute("data-hover-stop", "same-definition");
        });
      }
      value.querySelectorAll(".type-node[data-hover-stop]").forEach(function (node) {
        node.replaceWith.apply(node, Array.from(node.childNodes));
      });
    }
    function namePopupEntry(target) {
      var shell = target && target.closest && target.closest(".name-hover-popup");
      return shell && namePopups.find(function (entry) { return entry.popup === shell; });
    }
    function namePopupContains(target) {
      return Boolean(namePopupEntry(target));
    }
    function nodeOwnsOpenHover(node) {
      return Boolean(node && namePopups.some(function (entry) {
        return node.contains(entry.anchor);
      }));
    }
    function removeNamePopupsFrom(index) {
      if (index < 0 || index >= namePopups.length) return;
      nameRequest += 1;
      var removedRangeScope = false;
      namePopups.splice(index).forEach(function (entry) {
        window.clearTimeout(entry.closeTimer);
        if (entry.popup === rangeScope) removedRangeScope = true;
        entry.popup.remove();
        if (entry.activeName) entry.activeName.classList.remove("name-active");
        if (entry.activeNode) entry.activeNode.classList.remove("type-active");
      });
      if (removedRangeScope) setRangeScope(fallbackRangeScope());
    }
    function hideName() {
      clearLeafNameHighlight();
      if (namePopups.length) removeNamePopupsFrom(0);
      else nameRequest += 1;
    }
    function cancelNameClose(entry) {
      while (entry) {
        window.clearTimeout(entry.closeTimer);
        entry.closeTimer = null;
        entry = entry.parent;
      }
      cancelHide();
    }
    function nameBranchHovered(entry) {
      var index = namePopups.indexOf(entry);
      if (index < 0) return false;
      return namePopups.slice(index).some(function (candidate) {
        return (candidate.anchor.matches && candidate.anchor.matches(":hover"))
          || (candidate.popup.matches && candidate.popup.matches(":hover"));
      });
    }
    function laterHideName(entry) {
      if (!entry) return;
      window.clearTimeout(entry.closeTimer);
      entry.closeTimer = scheduleHoverClose(function () {
        if (nameBranchHovered(entry)) {
          cancelNameClose(entry);
          return;
        }
        var index = namePopups.indexOf(entry);
        if (index >= 0) removeNamePopupsFrom(index);
      });
    }
    function positionNameEntry(entry) {
      if (!entry.popup.isConnected || !entry.anchor.isConnected) return;
      var rect = entry.anchor.getBoundingClientRect();
      var width = Math.min(entry.popup.offsetWidth, window.innerWidth - 16);
      entry.popup.style.left = (window.scrollX + Math.max(8,
        Math.min(rect.left, window.innerWidth - width - 8))) + "px";
      /* Every level opens below its source. The document can keep growing and
         scrolling; a crowded viewport never makes a child jump above its parent. */
      entry.popup.style.top = (window.scrollY + rect.bottom) + "px";
    }
    function positionName() {
      namePopups.forEach(positionNameEntry);
    }
    function showName(name) {
      var identity = hoverIdentity(name);
      if (name && name.getAttribute && name.getAttribute("data-hover-stop")) {
        /* Terminal names have no hover and must not select a structural node. */
        clearLeafNameHighlight();
        var shell = name.closest && name.closest(".hover-popup");
        if (shell) shell.querySelectorAll(".type-node.type-active").forEach(function (node) {
          node.classList.remove("type-active");
        });
        return;
      }
      if (identity && namePopups.some(function (entry) {
        return entry.identity === identity;
      })) {
        /* A universe popup may still inspect its Type leaf.  Stop only when
           that same definition recurs inside its own signature, preventing a
           Type → Type → … cycle without disabling the leaf interaction. */
        if (compactPointer.matches && name.matches && name.matches("a[data-type]")) {
          clearLeafNameHighlight();
          leafActiveName = name;
          leafActiveName.classList.add("name-active");
        }
        return;
      }
      clearLeafNameHighlight();
      var parent = namePopupEntry(name);
      /* Starting a child lookup is already part of the parent's hover path.
         Cancel the whole ancestor branch before the asynchronous fetch, so a
         pending parent timeout cannot tear down the child as it appears. */
      if (parent) cancelNameClose(parent);
      var parentIndex = parent ? namePopups.indexOf(parent) : -1;
      var existing = namePopups[parentIndex + 1];
      if (existing && existing.anchor === name) {
        cancelNameClose(existing);
        return;
      }
      var serial = ++nameRequest;
      var expressionType = name.getAttribute("data-expression-type");
      var rawSpec = expressionType || name.getAttribute("data-type");
      var spec = rawSpec ? rawSpec.split("#") : null;
      (spec ? fetchTypes(spec[0]) : Promise.resolve({})).then(function (types) {
        var expression = expressionType && spec && types.$expressions
          && types.$expressions[spec[1]];
        var html = expressionType ? expression && expression.type
          : spec && types[spec[1]];
        var hasDefinition = name.hasAttribute("href");
        if (serial !== nameRequest || !name.isConnected
            || (parent && namePopups.indexOf(parent) < 0)
            || (!compactPointer.matches && name.matches && !name.matches(":hover"))
            || (!html && !(compactPointer.matches && hasDefinition))) return;
        removeNamePopupsFrom(parentIndex + 1);
        var namePopup = document.createElement("div");
        namePopup.className = "hover-popup name-hover-popup Agda";
        namePopup.setAttribute("role", "dialog");
        namePopup.dataset.hoverDepth = String(parentIndex + 1);
        if (hasDefinition) namePopup.classList.add("has-definition-link");
        var nameValue = document.createElement("div");
        nameValue.className = "type-value Agda";
        if (html) nameValue.innerHTML = html;
        else nameValue.textContent = name.textContent.trim();
        markTerminalHoverStops(nameValue, identity);
        if (isUniverseTypeText(nameValue.textContent))
          namePopup.classList.add("hover-terminal");
        namePopup.appendChild(nameValue);
        if (hasDefinition) namePopup.appendChild(definitionAction(name.href,
          name.getAttribute("data-name") || name.textContent.trim()));
        document.body.appendChild(namePopup);
        /* A leaf identifier and a structural type node are different targets.
           Reuse the source-code name highlight for the former; otherwise the
           nearest enclosing structural span wrongly lights up as one node. */
        var activeName = name.matches && name.matches("a[data-type]") ? name : null;
        var activeNode = name.matches && name.matches(".type-node") ? name : null;
        if (activeName) activeName.classList.add("name-active");
        if (activeNode) activeNode.classList.add("type-active");
        var entry = { popup: namePopup, anchor: name, parent: parent,
          identity: identity,
          activeName: activeName, activeNode: activeNode, closeTimer: null };
        namePopups.push(entry);
        if (compactPointer.matches && rangeCapableScope(namePopup)) {
          var gestureScope = levelGesture && levelGesture.activated
            && levelGesture.kind === "type" && levelGesture.scope;
          setRangeScope(gestureScope || namePopup);
        }
        cancelNameClose(entry);
        namePopup.addEventListener("mouseenter", function () { cancelNameClose(entry); });
        namePopup.addEventListener("mouseleave", function () { laterHideName(entry); });
        namePopup.addEventListener("focusin", function () { cancelNameClose(entry); });
        namePopup.addEventListener("focusout", function (event) {
          if (!event.relatedTarget || !namePopup.contains(event.relatedTarget)) laterHideName(entry);
        });
        positionNameEntry(entry);
      });
    }

    function activateTypeNode(target) {
      var node = target && target.closest && target.closest(".type-value .type-node");
      var shell = node && node.closest(".hover-popup");
      if (!shell) return null;
      shell.querySelectorAll(".type-node.type-active").forEach(function (active) {
        if (active !== node) active.classList.remove("type-active");
      });
      node.classList.add("type-active");
      return node;
    }
    function activateTypeGestureItem(item) {
      clearHighlight(item.node.closest(".hover-popup"));
      showName(item.node);
      if (item.kind === "name") {
        leafActiveName = item.node;
        leafActiveName.classList.add("name-active");
      } else {
        activateTypeNode(item.node);
      }
    }

    var popup = document.createElement("div");
    popup.className = "hover-popup type-inspector";
    popup.setAttribute("role", "dialog");
    popup.hidden = true;
    popup.innerHTML = '<div class="type-value Agda"></div>' +
      '<a class="type-definition-link" hidden></a>';
    document.body.appendChild(popup);
    var swipeHint = document.createElement("div");
    swipeHint.className = "ast-swipe-hint";
    swipeHint.setAttribute("role", "status");
    swipeHint.textContent = swipeHintCopy;
    swipeHint.hidden = true;
    document.body.appendChild(swipeHint);
    var value = popup.querySelector(".type-value");
    var definitionLink = popup.querySelector(".type-definition-link");
    definitionLink.setAttribute("aria-label", definitionCopy);
    definitionLink.title = definitionCopy;
    definitionLink.innerHTML = definitionActionIcon;
    var options = [], selected = null, anchor = null, renderedRequest = 0;
    var levelGesture = null;
    var rangeScope = null;
    var pinned = false;
    var request = 0;
    var hideTimer = null;

    function expressionAncestors(target) {
      var node = target.closest && target.closest(".expr-node");
      var result = [];
      while (node) {
        result.push(node);
        node = node.parentElement && node.parentElement.closest(".expr-node");
      }
      return result;
    }
    function containingExpressionData(expressionData, start, end) {
      return Object.keys(expressionData).map(function (expressionId) {
        return { id: expressionId, data: expressionData[expressionId] };
      }).filter(function (entry) {
        return entry.data && entry.data.start <= start && entry.data.end >= end;
      });
    }
    function expressionOptions(expressionData, directNode) {
      if (!directNode) return [];
      var start = Number(directNode.dataset.exprStart);
      var end = Number(directNode.dataset.exprEnd);
      var block = directNode.closest("pre.Agda");
      if (!Number.isFinite(start) || !Number.isFinite(end) || !block) return [];
      var representatives = new Map();
      block.querySelectorAll(".expr-node").forEach(function (node) {
        if (!representatives.has(node.dataset.exprId))
          representatives.set(node.dataset.exprId, node);
      });
      return containingExpressionData(expressionData, start, end).map(function (entry) {
        var data = entry.data;
        var node = representatives.get(entry.id);
        return node && { kind: "expression", node: node, source: data.source,
                         type: data.type, start: data.start, end: data.end,
                         astKind: data.kind };
      }).filter(Boolean);
    }
    function usesInspector(target) {
      /* Expression spans are emitted only inside Agda blocks, and only for
         applications. Inline/display Agda and a bare block identifier therefore
         keep the original name-type popup. */
      return expressionAncestors(target).length > 0;
    }
    function clearHighlight(scope) {
      leafActiveName = null;
      (scope || document).querySelectorAll(".expr-active, .name-active, .type-active, .occ").forEach(function (node) {
        node.classList.remove("expr-active", "name-active", "type-active", "occ");
      });
    }
    function position() {
      if (popup.hidden || !anchor) return;
      var rect = anchor.getBoundingClientRect();
      var width = Math.min(popup.offsetWidth, window.innerWidth - 16);
      var left = Math.max(8, Math.min(rect.left, window.innerWidth - width - 8));
      popup.style.left = (window.scrollX + left) + "px";
      popup.style.top = (window.scrollY + rect.bottom) + "px";
      popup.style.maxHeight = compactPointer.matches ? "calc(100vh - 1rem)" : "none";
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
      markTerminalHoverStops(value, hoverIdentity(anchor));
      popup.classList.toggle("hover-terminal", isUniverseTypeText(value.textContent));
      if (compactPointer.matches && option.href) {
        definitionLink.href = option.href;
        definitionLink.setAttribute("data-name", option.source);
        definitionLink.hidden = false;
        popup.classList.add("has-definition-link");
      } else {
        definitionLink.removeAttribute("href");
        definitionLink.removeAttribute("data-name");
        definitionLink.hidden = true;
        popup.classList.remove("has-definition-link");
      }
      setPopupWidth(option);
      clearHighlight();
      if (option.kind === "name" && option.nameNode)
        option.nameNode.classList.add("name-active");
      else if (option.node) {
        var block = option.node.closest("pre.Agda");
        var expressionId = option.node.dataset.exprId;
        (block ? block.querySelectorAll(".expr-node") : [option.node]).forEach(function (node) {
          if (node.dataset.exprId === expressionId) node.classList.add("expr-active");
        });
      }
      requestAnimationFrame(position);
    }
    function gestureIndex(deltaX) {
      var distance = Math.abs(deltaX);
      if (distance < 12) return -1;
      return Math.floor((distance - 12) / 28);
    }
    function gestureCandidates(items, base, deltaX) {
      if (!base) return [];
      var chain = [];
      var current = base;
      items.filter(function (item) {
        return item.kind === "expression"
          && item.start <= base.start && item.end >= base.end;
      }).sort(function (left, right) {
        var widthDifference = (left.end - left.start) - (right.end - right.start);
        return widthDifference || right.start - left.start;
      }).forEach(function (item) {
        /* Source ranges should nest like matched brackets. Ignore crossing
           ranges rather than letting them introduce an unreachable boundary. */
        if (item.start <= current.start && item.end >= current.end) {
          chain.push(item);
          current = item;
        }
      });
      var byBoundary = new Map();
      var movingRight = deltaX > 0;
      chain.forEach(function (item) {
        var boundary = movingRight ? item.end : item.start;
        if (movingRight ? boundary <= base.end : boundary >= base.start) return;
        /* Coincident edges are one visual boundary. Because the chain runs
           inside-out, the last node at that edge is the one being entered. */
        byBoundary.set(boundary, item);
      });
      return Array.from(byBoundary.values()).sort(function (left, right) {
        return movingRight ? left.end - right.end : right.start - left.start;
      });
    }
    function applyLevelGesture() {
      if (!levelGesture || !levelGesture.activated) return;
      if (levelGesture.kind === "type") {
        var typeBase = levelGesture.baseOption;
        var typeStep = gestureIndex(levelGesture.deltaX);
        var typeCandidates = gestureCandidates(
          levelGesture.items, typeBase, levelGesture.deltaX
        );
        var typeNext = typeStep < 0 || !typeCandidates.length
          ? typeBase : typeCandidates[Math.min(typeStep, typeCandidates.length - 1)];
        if (typeNext && typeNext !== levelGesture.lastOption) {
          levelGesture.lastOption = typeNext;
          activateTypeGestureItem(typeNext);
          vibrateSelection();
        }
        if (levelGesture && levelGesture.released) clearLevelGesture();
        return;
      }
      if (!options.length || levelGesture.request !== request
          || levelGesture.request !== renderedRequest) return;
      if (!levelGesture.baseOption) {
        levelGesture.baseOption = selected;
        levelGesture.lastOption = selected;
      }
      var base = levelGesture.baseOption;
      var step = gestureIndex(levelGesture.deltaX);
      var candidates = gestureCandidates(options, base, levelGesture.deltaX);
      var next = step < 0 || !candidates.length
        ? base : candidates[Math.min(step, candidates.length - 1)];
      if (!next || next === levelGesture.lastOption) {
        if (levelGesture.released) clearLevelGesture();
        return;
      }
      levelGesture.lastOption = next;
      choose(options.indexOf(next), true);
      if (levelGesture && levelGesture.released) clearLevelGesture();
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
        measure.appendChild(definitionAction(item.href, item.source));
      }
      document.body.appendChild(measure);
      popup.style.width = Math.ceil(measure.getBoundingClientRect().width) + "px";
      measure.remove();
    }
    function rangeCapableScope(scope) {
      if (scope && scope.classList.contains("hover-terminal")) return null;
      return scope && scope.querySelector(
        ".expr-node, .type-node[data-expression-type]"
      ) ? scope : null;
    }
    function setRangeScope(scope) {
      var next = rangeCapableScope(scope);
      if (rangeScope && rangeScope !== next)
        rangeScope.classList.remove("ast-ranges-visible");
      rangeScope = next;
      if (rangeScope) rangeScope.classList.add("ast-ranges-visible");
      swipeHint.hidden = !(compactPointer.matches && rangeScope);
      return Boolean(rangeScope);
    }
    function typeGestureState(target) {
      var direct = target && target.closest
        && target.closest(".type-value .type-node[data-expression-type]");
      var name = target && target.closest
        && target.closest(".type-value a[data-type]");
      var valueScope = direct && direct.closest(".type-value");
      var popupScope = direct && direct.closest(".hover-popup");
      if (!direct || !valueScope || !popupScope
          || direct.hasAttribute("data-hover-stop")
          || popupScope.classList.contains("hover-terminal")) return null;
      var items = Array.from(
        valueScope.querySelectorAll(".type-node[data-expression-type]")
      ).map(function (node) {
        return { kind: "expression", node: node,
          start: Number(node.dataset.exprStart), end: Number(node.dataset.exprEnd) };
      }).filter(function (item) {
        return Number.isFinite(item.start) && Number.isFinite(item.end);
      });
      var base = items.find(function (item) { return item.node === direct; });
      if (name && valueScope.contains(name) && !name.hasAttribute("data-hover-stop")) {
        /* The compiler traces structural ranges, while a linked identifier is
           a separate selectable leaf. Recover its offset in the same visible
           Unicode text used by the renderer, just as source-code gestures
           prepend their directly touched name to the expression chain. */
        var before = document.createRange();
        before.setStart(valueScope, 0);
        before.setEndBefore(name);
        var start = Array.from(before.toString()).length;
        var leaf = { kind: "name", node: name, start: start,
          end: start + Array.from(name.textContent).length };
        items.unshift(leaf);
        base = leaf;
      }
      return base ? { scope: popupScope, items: items, base: base } : null;
    }
    function fallbackRangeScope() {
      for (var index = namePopups.length - 1; index >= 0; index--) {
        if (rangeCapableScope(namePopups[index].popup))
          return namePopups[index].popup;
      }
      if (!popup.hidden && rangeCapableScope(popup)) return popup;
      var block = anchor && anchor.closest && anchor.closest("pre.Agda");
      return rangeCapableScope(block);
    }
    function clearLevelGesture() {
      if (!levelGesture) return;
      window.clearTimeout(levelGesture.timer);
      if (levelGesture.scope) levelGesture.scope.classList.remove("ast-level-gesture");
      levelGesture = null;
    }
    function render(items, target, preferred) {
      cancelHide();
      options = items;
      anchor = target;
      var nextRangeBlock = target.closest && target.closest("pre.Agda");
      setRangeScope(nextRangeBlock);
      renderedRequest = request;
      popup.hidden = false;
      choose(Math.max(0, items.indexOf(preferred)));
      if (compactPointer.matches && rangeCapableScope(popup)) setRangeScope(popup);
      applyLevelGesture();
    }
    function show(target) {
      cancelHide();
      hideName();
      var serial = ++request;
      var name = target.closest && target.closest("a[data-type]");
      var linkedName = target.closest && target.closest("a[href]");
      var directNode = target.closest && target.closest(".expr-node");
      var codeScope = directNode && directNode.closest
        && directNode.closest("[data-module]");
      var pageModule = codeScope && codeScope.dataset.module;
      var pageRequest = directNode
        ? fetchTypes(pageModule || cfg.chapter || cfg.module) : Promise.resolve({});
      var nameSpec = name ? name.getAttribute("data-type").split("#") : null;
      var nameRequest = nameSpec ? fetchTypes(nameSpec[0]) : Promise.resolve({});
      Promise.all([pageRequest, nameRequest]).then(function (loaded) {
        if (serial !== request || !target.isConnected) return;
        var expressionData = loaded[0].$expressions || {};
        /* A multiline source node is rendered as several visual spans.  DOM
           ancestry therefore describes only the touched fragment, whereas the
           source intervals recover the complete logical AST chain. */
        var items = expressionOptions(expressionData, directNode);
        var nameType = nameSpec && loaded[1][nameSpec[1]];
        var chosenName = name || (compactPointer.matches ? linkedName : null);
        if (chosenName && (nameType || (compactPointer.matches
            && chosenName.hasAttribute("href")))) {
          var canonicalName = chosenName.getAttribute("data-name") ||
            (nameSpec && (loaded[1].$names || {})[nameSpec[1]]);
          /* The pointer is directly over this identifier, so its name type is
             preferred. Width follows the displayed type: reserving space for
             every enclosing application leaves short variable types in a large,
             mostly empty popup now that node selection happens in the source. */
          items.unshift({ kind: "name", node: null, nameNode: chosenName,
                          source: canonicalName || chosenName.textContent.trim(),
                          type: nameType || escapedCodeName(canonicalName ||
                            chosenName.textContent.trim()),
                          href: chosenName.hasAttribute("href") ? chosenName.href : null,
                          start: Number(chosenName.id || chosenName.dataset.sourcePosition),
                          end: Number(chosenName.id || chosenName.dataset.sourcePosition)
                            + Array.from(chosenName.textContent).length });
        }
        items.sort(function (left, right) {
          if (left.kind === "name") return right.kind === "name" ? 0 : -1;
          if (right.kind === "name") return 1;
          var leftWidth = left.end - left.start;
          var rightWidth = right.end - right.start;
          return leftWidth - rightWidth || right.start - left.start;
        });
        var preferred = chosenName
          ? items.find(function (item) { return item.kind === "name"; })
          : items.find(function (item) {
              return item.node.dataset.exprId === directNode.dataset.exprId;
            });
        if (items.length) render(items, chosenName || directNode || target,
                                 preferred || items[0]);
        else if (levelGesture && levelGesture.request === serial
                 && levelGesture.released) clearLevelGesture();
      });
    }
    function hide() {
      if (pinned) return;
      cancelHide();
      clearLevelGesture();
      request += 1;
      popup.hidden = true; options = []; selected = null; anchor = null; clearHighlight();
      setRangeScope(null);
      hideName();
    }
    function cancelHide() {
      window.clearTimeout(hideTimer);
      hideTimer = null;
    }
    function laterHide() {
      cancelHide();
      hideTimer = scheduleHoverClose(hide);
    }
    function activeSourceRangeContains(target) {
      if (!target) return false;
      if (selected && selected.kind === "name" && selected.nameNode)
        return selected.nameNode === target || selected.nameNode.contains(target);
      if (selected && selected.kind === "expression") {
        var expression = target.closest && target.closest(".expr-node");
        if (expression) {
          var start = Number(expression.dataset.exprStart);
          var end = Number(expression.dataset.exprEnd);
          if (Number.isFinite(start) && Number.isFinite(end)
              && selected.start <= start && selected.end >= end) return true;
        }
        var token = target.closest && target.closest("[id]");
        var position = token && Number(token.id);
        if (Number.isFinite(position)
            && selected.start <= position && position < selected.end) return true;
      }
      return namePopups.some(function (entry) {
        return entry.anchor === target || entry.anchor.contains(target);
      });
    }
    function hoverPopupContains(target) {
      return popup.contains(target) || namePopupContains(target);
    }
    function activeHoverChainContains(target) {
      return hoverPopupContains(target) || activeSourceRangeContains(target);
    }

    document.addEventListener("mouseover", function (event) {
      if (compactPointer.matches) return;
      activateTypeNode(event.target);
      if (!usesInspector(event.target)) return;
      var target = event.target.closest && event.target.closest(".expr-node, a[data-type]");
      if (!target || popup.contains(target)) return;
      var hovered = event.target;
      if (!hovered.isConnected || !hovered.matches(":hover")) return;
      pinned = false; show(hovered);
    });
    document.addEventListener("mouseout", function (event) {
      if (compactPointer.matches) return;
      var typeNode = event.target.closest
        && event.target.closest(".type-value .type-node");
      if (typeNode) {
        var nextTypeNode = event.relatedTarget && activateTypeNode(event.relatedTarget);
        if (nextTypeNode !== typeNode && !nodeOwnsOpenHover(typeNode))
          typeNode.classList.remove("type-active");
      }
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
        /* Touch browsers normally activate on pointerdown. Keep click as a
           fallback for keyboard and synthetic activation. */
        var compactBlock = event.target.closest && event.target.closest("pre.Agda");
        var touched = definitionHoverTarget(event.target);
        if (compactBlock && setRangeScope(compactBlock)) pinned = true;
        else if (!touched && !activeHoverChainContains(event.target)) {
          pinned = false;
          hide(); hideName();
        }
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
    popup.addEventListener("mouseenter", cancelHide);
    popup.addEventListener("mouseleave", laterHide);
    document.addEventListener("pointerdown", function (event) {
      if (!compactPointer.matches) {
        if (!popup.hidden && !popup.contains(event.target)
            && !(event.target.closest && event.target.closest(
              ".expr-node, a[data-type], .type-node[data-expression-type]"
            ))) {
          pinned = false; hide();
        }
        return;
      }
      var codeBlock = event.target.closest && event.target.closest("pre.Agda");
      var target = definitionHoverTarget(event.target);
      var rangeCapableBlock = rangeCapableScope(codeBlock);
      var typeGesture = typeGestureState(event.target);
      var insideHoverPopup = hoverPopupContains(event.target);
      var hasActiveHover = !popup.hidden || Boolean(namePopups.length);
      if (hasActiveHover && !activeHoverChainContains(event.target)) {
        pinned = false;
        hide(); hideName();
      }
      /* A code block without compiler-backed expression ranges still contains
         ordinary typed names.  It cannot start a range-swipe gesture, but its
         names must enter the same hover path as names in richer Agda blocks. */
      if (codeBlock && !rangeCapableBlock && !target) {
        pinned = false;
        hide(); hideName();
        return;
      }
      if (rangeCapableBlock && setRangeScope(rangeCapableBlock)) pinned = true;
      if (typeGesture) setRangeScope(typeGesture.scope);
      if (codeBlock && !target) {
        return;
      }
      if (insideHoverPopup
          && !(target && target.matches(
            "a[data-type], .type-node[data-expression-type]"
          ))) return;
      if (!target) {
        pinned = false; hide(); hideName();
        return;
      }
      if (usesInspector(event.target)) {
        return;
      } else if (target.matches("a[href], .type-node[data-expression-type]")) {
        clearLevelGesture();
        pinned = false;
        /* Keep the popup containing this target visible.  The child hover is
           positioned from that live anchor, exactly as in the desktop path. */
        if (!insideHoverPopup && !popup.hidden) hide();
        showName(target);
      }
    });
    document.addEventListener("touchstart", function (event) {
      if (!compactPointer.matches || event.touches.length !== 1) return;
      var block = event.target.closest && event.target.closest("pre.Agda");
      var continuesActiveBlock = block && block === rangeScope && options.length;
      var touchesExpression = usesInspector(event.target);
      var typeGesture = typeGestureState(event.target);
      if (!continuesActiveBlock && !touchesExpression && !typeGesture) return;
      var touch = event.touches[0];
      var gesture = {
        kind: typeGesture ? "type" : "source",
        target: event.target,
        block: block,
        scope: typeGesture ? typeGesture.scope : block,
        startX: touch.clientX,
        startY: touch.clientY,
        deltaX: 0,
        activated: false,
        touchesExpression: touchesExpression,
        lastOption: typeGesture && typeGesture.base,
        items: typeGesture && typeGesture.items,
        baseOption: typeGesture && typeGesture.base
      };
      clearLevelGesture();
      levelGesture = gesture;
      gesture.timer = window.setTimeout(function () {
        if (levelGesture !== gesture) return;
        gesture.activated = true;
        if (gesture.scope) gesture.scope.classList.add("ast-level-gesture");
        vibrateSelection();
        if (gesture.kind === "type") {
          setRangeScope(gesture.scope);
          activateTypeGestureItem(gesture.baseOption);
          return;
        }
        hideName(); pinned = true;
        if (gesture.touchesExpression) {
          show(gesture.target);
          gesture.request = request;
        } else if (gesture.block === rangeScope && options.length) {
          gesture.request = request;
          applyLevelGesture();
        } else {
          show(gesture.target);
          gesture.request = request;
        }
      }, 300);
    });
    document.addEventListener("selectstart", function (event) {
      if (!compactPointer.matches) return;
      var expression = event.target.closest
        && event.target.closest(".expr-node, .type-node[data-expression-type]");
      if (expression) event.preventDefault();
    });
    document.addEventListener("touchmove", function (event) {
      if (!compactPointer.matches || !levelGesture || event.touches.length !== 1) return;
      var touch = event.touches[0];
      var deltaX = touch.clientX - levelGesture.startX;
      var deltaY = touch.clientY - levelGesture.startY;
      if (!levelGesture.activated) {
        if (Math.hypot(deltaX, deltaY) >= 10) {
          clearLevelGesture();
        }
        return;
      }
      /* A completed hold owns the gesture. Suppress vertical page movement and
         interpret only its horizontal component as AST-level selection. */
      event.preventDefault();
      levelGesture.deltaX = deltaX;
      applyLevelGesture();
    }, { passive: false });
    function finishLevelGesture(event) {
      if (!levelGesture) return;
      var gesture = levelGesture;
      window.clearTimeout(gesture.timer);
      if (!gesture.activated) {
        var target = gesture.target;
        clearLevelGesture();
        if (event.type === "touchend" && gesture.kind === "source") {
          vibrateSelection();
          hideName(); pinned = true; show(target);
        }
        return;
      }
      if (gesture.scope) gesture.scope.classList.remove("ast-level-gesture");
      if (gesture.kind === "type") {
        clearLevelGesture();
        setRangeScope(fallbackRangeScope());
        return;
      }
      if (event.type === "touchcancel"
          || gesture.request === renderedRequest) clearLevelGesture();
      else gesture.released = true;
    }
    document.addEventListener("touchend", finishLevelGesture);
    document.addEventListener("touchcancel", finishLevelGesture);
    document.addEventListener("keydown", function (event) {
      if (event.key === "Escape") { pinned = false; hide(); hideName(); }
    });
    document.addEventListener("mouseover", function (event) {
      if (compactPointer.matches) return;
      var name = event.target.closest && event.target.closest(
        "a[data-type], .type-node[data-expression-type]"
      );
      if (!name || usesInspector(event.target)
          || (event.relatedTarget && name.contains(event.relatedTarget))) return;
      /* A type rendered inside the inspector can itself be inspected. */
      if (!popup.contains(name) && !namePopupEntry(name)) {
        pinned = false;
        if (!popup.hidden) hide();
      }
      if (!name.isConnected || !name.matches(":hover")) return;
      showName(name);
    });
    document.addEventListener("mouseout", function (event) {
      if (compactPointer.matches) return;
      var name = event.target.closest && event.target.closest(
        "a[data-type], .type-node[data-expression-type]"
      );
      if (name && !usesInspector(event.target)
          && (!event.relatedTarget || (!name.contains(event.relatedTarget)
              && !namePopupContains(event.relatedTarget)))) {
        var child = namePopups.find(function (entry) { return entry.anchor === name; });
        laterHideName(child);
      }
    });
    (modalReadingScroller() || window).addEventListener("scroll", function () {
      position(); positionName();
    }, { passive: true });
    window.addEventListener("resize", function () {
      if (!popup.hidden && selected) setPopupWidth(selected);
      position(); positionName();
    });
    document.addEventListener("bedrock:definition-modal-open", function () {
      pinned = false;
      hide();
      hideName();
    });
  }

  function alignModalDefinition(frameDocument, targetBlock) {
    var scroller = frameDocument.getElementById("main-content");
    if (!scroller) return false;
    var scrollerTop = scroller.getBoundingClientRect().top;
    var bar = frameDocument.getElementById("section-sticky");
    /* The retained chapter directory is the only chrome inside the scroller.
       Use its actual edge in the same coordinate system as the target block. */
    var inset = bar ? Math.max(0, bar.getBoundingClientRect().bottom - scrollerTop) : 0;
    var delta = targetBlock.getBoundingClientRect().top - scrollerTop - inset;
    if (Math.abs(delta) <= 0.5) return false;
    var desiredTop = scroller.scrollTop + delta;
    var maximumTop = scroller.scrollHeight - scroller.clientHeight;
    if (desiredTop > maximumTop) {
      var root = frameDocument.documentElement;
      var room = parseFloat(root.style.getPropertyValue("--definition-modal-anchor-room")) || 0;
      root.style.setProperty("--definition-modal-anchor-room",
        Math.ceil(room + desiredTop - maximumTop + 1) + "px");
    }
    /* On iOS Safari the iframe window is not a reliable scrolling element.
       Both the measurement and the write belong to the explicit reading scroller. */
    scroller.scrollTop = desiredTop;
    return true;
  }

  function sizeModalReadingScroller(frameDocument, modalBody) {
    var scroller = frameDocument.getElementById("main-content");
    if (!scroller) return null;
    /* Use the actual dialog height for the shared desktop/phone reading area. */
    var height = modalBody.clientHeight;
    if (height > 0) {
      frameDocument.documentElement.style.height = height + "px";
      frameDocument.body.style.height = height + "px";
      scroller.style.height = height + "px";
    }
    return scroller;
  }

  function definitionPageKey(url) {
    var page = new URL(url.href);
    page.hash = "";
    page.searchParams.delete("bedrock-modal");
    page.searchParams.delete("bedrock-modal-scroll");
    page.searchParams.sort();
    /* Static hosts canonicalize .html to extensionless URLs (and index.html
       to a directory). Those redirects still identify the same document. */
    page.pathname = page.pathname.replace(/\/index\.html$/, "/")
      .replace(/\.html$/, "").replace(/\/$/, "") || "/";
    return page.href;
  }

  /* ---- in-page definition previews --------------------------------------- */
  function initDefinitionModals() {
    var history = [], historyIndex = -1, view = null, loadRequest = 0;
    var isModalDocument = isDefinitionModalDocument;
    var copy = ({
      en: { title: "Definition", loading: "Loading definition…",
        missing: "The target definition could not be loaded from this page.", close: "Close",
        back: "Back", forward: "Forward" },
      zh: { title: "定义", loading: "正在载入定义…",
        missing: "无法从该页面载入目标定义。", close: "关闭",
        back: "后退", forward: "前进" },
      ja: { title: "定義", loading: "定義を読み込んでいます…",
        missing: "このページから対象の定義を読み込めませんでした。", close: "閉じる",
        back: "戻る", forward: "進む" }
    })[cfg.lang] || {
      title: "Definition", loading: "Loading definition…",
      missing: "The target definition could not be loaded from this page.", close: "Close",
      back: "Back", forward: "Forward"
    };

    function targetFor(link) {
      if (!link || link.classList.contains("definition-modal-title")) return null;
      var raw = link.getAttribute("href");
      if (!raw) return null;
      var url;
      try { url = new URL(raw, document.baseURI); } catch (_) { return null; }
      if (!url.hash || url.origin !== location.origin) return null;
      url.searchParams.delete("bedrock-modal");
      url.searchParams.delete("bedrock-modal-scroll");
      var spec = link.getAttribute("data-type");
      var filename = decodeURIComponent(url.pathname.split("/").pop() || "");
      return { url: url, module: spec ? spec.split("#")[0] : filename.replace(/\.html$/, "") };
    }
    function close() {
      if (!view) return;
      var focus = view.opener;
      if (view.frameSizeObserver) view.frameSizeObserver.disconnect();
      view.backdrop.remove();
      view = null;
      history = [];
      historyIndex = -1;
      loadRequest++;
      document.body.classList.remove("definition-modal-open");
      if (focus && focus.isConnected && focus.focus) focus.focus({ preventScroll: true });
    }
    function createView(opener) {
      var backdrop = document.createElement("div");
      backdrop.className = "definition-modal-backdrop";
      var modal = document.createElement("section");
      modal.className = "definition-modal";
      modal.setAttribute("role", "dialog");
      modal.setAttribute("aria-modal", "true");
      var titleId = "definition-modal-title-" + Date.now();
      modal.setAttribute("aria-labelledby", titleId);
      var header = document.createElement("header");
      header.className = "definition-modal-header";
      var title = document.createElement("a");
      title.className = "definition-modal-title";
      title.id = titleId;
      title.textContent = copy.title;
      var historyActions = document.createElement("div");
      historyActions.className = "definition-modal-history";
      var back = document.createElement("button");
      back.className = "definition-modal-history-button";
      back.type = "button";
      back.setAttribute("aria-label", copy.back);
      back.title = copy.back;
      back.textContent = "←";
      var forward = document.createElement("button");
      forward.className = "definition-modal-history-button";
      forward.type = "button";
      forward.setAttribute("aria-label", copy.forward);
      forward.title = copy.forward;
      forward.textContent = "→";
      var closeButton = document.createElement("button");
      closeButton.className = "definition-modal-close";
      closeButton.type = "button";
      closeButton.setAttribute("aria-label", copy.close);
      closeButton.textContent = "×";
      var body = document.createElement("div");
      body.className = "definition-modal-body";
      body.setAttribute("aria-live", "polite");
      historyActions.appendChild(back);
      historyActions.appendChild(forward);
      header.appendChild(historyActions);
      header.appendChild(title);
      header.appendChild(closeButton);
      modal.appendChild(header);
      modal.appendChild(body);
      backdrop.appendChild(modal);
      document.body.appendChild(backdrop);
      view = { backdrop: backdrop, modal: modal, opener: opener, title: title,
        body: body, back: back, forward: forward, frame: null,
        frameSizeObserver: null };
      document.body.classList.add("definition-modal-open");
      closeButton.addEventListener("click", close);
      backdrop.addEventListener("pointerdown", function (event) {
        if (event.target === backdrop) close();
      });
      back.addEventListener("click", function () {
        if (historyIndex <= 0) return;
        historyIndex--;
        renderHistoryEntry();
      });
      forward.addEventListener("click", function () {
        if (historyIndex >= history.length - 1) return;
        historyIndex++;
        renderHistoryEntry();
      });
      closeButton.focus({ preventScroll: true });
    }
    function renderHistoryEntry() {
      if (!view || historyIndex < 0) return;
      if (view.frameSizeObserver) {
        view.frameSizeObserver.disconnect();
        view.frameSizeObserver = null;
      }
      var entry = history[historyIndex];
      var request = ++loadRequest;
      view.title.textContent = entry.label;
      view.title.href = entry.target.url.href;
      view.back.disabled = historyIndex === 0;
      view.forward.disabled = historyIndex === history.length - 1;
      view.body.textContent = copy.loading;
      var frame = document.createElement("iframe");
      frame.className = "definition-modal-frame";
      frame.title = entry.label;
      var frameUrl = new URL(entry.target.url.href);
      frameUrl.searchParams.set("bedrock-modal", "1");
      /* A frame URL with a fragment starts a second, native anchor scroll which
         can race the code-block alignment, especially in mobile WebKit. */
      frameUrl.hash = "";
      frame.addEventListener("load", function () {
        if (!view || request !== loadRequest || view.frame !== frame) return;
        var frameDocument, loadedUrl;
        try {
          frameDocument = frame.contentDocument;
          loadedUrl = new URL(frame.contentWindow.location.href);
        } catch (_) { return; }
        if (definitionPageKey(loadedUrl) !== definitionPageKey(entry.target.url)) {
          view.body.textContent = copy.missing;
          return;
        }
        var id;
        try { id = decodeURIComponent(entry.target.url.hash.slice(1)); }
        catch (_) { id = entry.target.url.hash.slice(1); }
        var target = frameDocument && frameDocument.getElementById(id);
        if (!target) {
          view.body.textContent = copy.missing;
          return;
        }
        var targetBlock = target.closest("pre.Agda") || target;
        var scroller = sizeModalReadingScroller(frameDocument, view.body);
        if (!scroller) {
          view.body.textContent = copy.missing;
          return;
        }
        var alignmentRun = 0;
        function alignTarget() {
          if (!alignmentActive || !view || request !== loadRequest || view.frame !== frame
              || !targetBlock.isConnected) return false;
          return alignModalDefinition(frameDocument, targetBlock);
        }
        function requestAlignment() {
          if (!alignmentActive) return;
          var run = ++alignmentRun;
          function settle(remaining) {
            if (!alignmentActive || run !== alignmentRun) return;
            var pending = alignTarget();
            if (pending && remaining > 0)
              frame.contentWindow.requestAnimationFrame(function () {
                settle(remaining - 1);
              });
          }
          settle(8);
        }
        var alignmentActive = true;
        var alignmentObserver = null;
        function stopAlignment() {
          alignmentActive = false;
          alignmentRun += 1;
          if (alignmentObserver) alignmentObserver.disconnect();
        }
        ["pointerdown", "touchstart", "wheel", "keydown"].forEach(function (type) {
          frame.contentWindow.addEventListener(type, stopAlignment,
            { capture: true, passive: type !== "keydown", once: true });
        });
        requestAlignment();
        if (frameDocument.fonts && frameDocument.fonts.ready) {
          frameDocument.fonts.ready.then(function () {
            frame.contentWindow.requestAnimationFrame(requestAlignment);
          });
        }
        if (frame.contentWindow.ResizeObserver) {
          alignmentObserver = new frame.contentWindow.ResizeObserver(function () {
            frame.contentWindow.requestAnimationFrame(requestAlignment);
          });
          alignmentObserver.observe(targetBlock);
          if (targetBlock.parentElement) alignmentObserver.observe(targetBlock.parentElement);
          var article = frameDocument.querySelector("article");
          if (article) alignmentObserver.observe(article);
          alignmentObserver.observe(scroller);
        }
        if (window.ResizeObserver) {
          view.frameSizeObserver = new ResizeObserver(function () {
            if (!view || request !== loadRequest || view.frame !== frame) return;
            sizeModalReadingScroller(frameDocument, view.body);
            requestAlignment();
          });
          view.frameSizeObserver.observe(view.body);
        }
        frame.contentWindow.addEventListener("resize", requestAlignment, { passive: true });
      });
      view.frame = frame;
      frame.src = frameUrl.href;
      view.body.textContent = "";
      view.body.appendChild(frame);
    }
    function qualifiedLabel(target, name) {
      return name === target.module || name.indexOf(target.module + ".") === 0
        ? name : target.module + "." + name;
    }
    function push(target, label, opener) {
      document.dispatchEvent(new CustomEvent("bedrock:definition-modal-open"));
      if (!view) createView(opener);
      history.splice(historyIndex + 1);
      history.push({ target: target, label: label });
      historyIndex = history.length - 1;
      renderHistoryEntry();
    }

    function open(link, target) {
      var name = link.getAttribute("data-name")
        || link.textContent.trim() || target.module;
      push(target, qualifiedLabel(target, name), link);
    }

    document.addEventListener("click", function (event) {
      if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
      var clickedLink = event.target.closest && event.target.closest("a[href]");
      if (!clickedLink) return;
      var definitionLink = clickedLink.matches(
        ".Agda a[href], .type-definition-link[href]"
      ) ? clickedLink : null;
      var target = targetFor(definitionLink);
      if (!target) {
        if (isModalDocument && window.parent !== window) {
          var pageTarget;
          try { pageTarget = new URL(clickedLink.href, document.baseURI); }
          catch (_) { return; }
          pageTarget.searchParams.delete("bedrock-modal");
          pageTarget.searchParams.delete("bedrock-modal-scroll");
          event.preventDefault();
          event.stopPropagation();
          window.parent.postMessage({ type: "bedrock-page-navigate",
            href: pageTarget.href }, location.origin);
        }
        return;
      }
      if (compactPointer.matches && !isDefinitionPopupAction(definitionLink)) {
        /* The hover subsystem owns this first tap. Its explicit arrow is the
           only compact-pointer action that advances from hover to modal. */
        return;
      }
      event.preventDefault();
      event.stopPropagation();
      if (isModalDocument && window.parent !== window) {
        var embeddedName = definitionLink.getAttribute("data-name")
          || definitionLink.textContent.trim() || target.module;
        window.parent.postMessage({ type: "bedrock-definition-open",
          href: target.url.href, module: target.module,
          label: qualifiedLabel(target, embeddedName) }, location.origin);
        return;
      }
      open(definitionLink, target);
    });
    window.addEventListener("message", function (event) {
      if (!view || event.origin !== location.origin
          || !view.frame || event.source !== view.frame.contentWindow
          || !event.data) return;
      if (event.data.type === "bedrock-page-navigate") {
        var pageUrl;
        try { pageUrl = new URL(event.data.href, document.baseURI); }
        catch (_) { return; }
        if (!/^(https?:|mailto:)$/.test(pageUrl.protocol)) return;
        location.href = pageUrl.href;
        return;
      }
      if (event.data.type !== "bedrock-definition-open") return;
      var targetUrl;
      try { targetUrl = new URL(event.data.href, document.baseURI); }
      catch (_) { return; }
      targetUrl.searchParams.delete("bedrock-modal");
      targetUrl.searchParams.delete("bedrock-modal-scroll");
      var current = history[historyIndex];
      if (current && definitionPageKey(current.target.url) === definitionPageKey(targetUrl)
          && current.target.url.hash === targetUrl.hash) {
        location.href = targetUrl.href;
        return;
      }
      push({ url: targetUrl, module: event.data.module }, event.data.label, view.opener);
    });
    document.addEventListener("keydown", function (event) {
      if (event.key !== "Escape") return;
      if (isModalDocument && window.parent !== window) {
        window.parent.postMessage({ type: "bedrock-definition-close" }, location.origin);
      } else if (view) {
        event.preventDefault();
        close();
      }
    });
    window.addEventListener("message", function (event) {
      if (view && event.origin === location.origin && view.frame
          && event.source === view.frame.contentWindow && event.data
          && event.data.type === "bedrock-definition-close") close();
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
      var link = target.closest && target.closest(
        "pre.Agda a[href], span.Agda a[href], .type-value a[href]"
      );
      return link && !link.hasAttribute("data-hover-stop") ? link : null;
    }
    function set(key, on) {
      document.querySelectorAll(
        "pre.Agda a[href], span.Agda a[href], .type-value a[href]"
      ).forEach(function (link) {
          if (occurrenceKey(link) === key) link.classList.toggle("occ", on);
        });
    }
    document.addEventListener("mouseover", function (event) {
      if (compactPointer.matches) return;
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
(function () {
  "use strict";
  document.addEventListener("DOMContentLoaded", function () {
    const figure = document.getElementById("fig-fiber-general");
    if (!figure) return;
    const trigger = figure.querySelector(".fiber-fan-stage");
    const bundles = Array.from(figure.querySelectorAll(".fiber-bundle"));
    if (!trigger || !bundles.length) return;
    const numbers = /-?\d+(?:\.\d+)?/g;
    const coordinates = data => data.match(numbers).map(Number);
    const position = node => [Number(node.getAttribute("cx")), Number(node.getAttribute("cy"))];
    const morphs = [], points = [], labels = [];
    const centreLabels = Array.from(figure.querySelectorAll(".fiber-center-label"));
    bundles.forEach(bundle => {
      const target = coordinates(bundle.dataset.centerPath);
      const [ax, iy] = target.slice(-2);
      const ay = position(bundle.querySelector(".fiber-domain-point"))[1];
      // Merge whole paths into p_i; the fixed base and the image remain distinct.
      const targets = [
        [".fiber-hair", target],
        [".fiber-moving-map", [ax, ay + 4, ax, iy - 10]],
        [".fiber-moving-tip", [ax - 4, iy - 17, ax, iy - 10, ax + 4, iy - 17]]
      ];
      targets.forEach(([selector, to]) => {
        bundle.querySelectorAll(selector).forEach(node => {
          morphs.push({node, to, from: coordinates(node.getAttribute("d")), template: node.getAttribute("d")});
        });
      });
      [[".fiber-domain-point", [ax, ay]], [".fiber-image-point", [ax, iy]]].forEach(([selector, to]) => {
        bundle.querySelectorAll(selector).forEach(node => points.push({node, to, from: position(node)}));
      });
      const width = bundle.ownerSVGElement.viewBox.baseVal.width;
      figure.querySelectorAll(`.fiber-sample-label[data-fiber="${bundle.dataset.fiber}"]`).forEach(node => {
        labels.push({node, from: parseFloat(node.style.left), to: ax / width * 100});
      });
    });
    const text = ({
      en: ["Contract the three fibres to their centres", "Expand the three fibres again"],
      zh: ["将三束纤维收向各自的中心", "重新展开三束纤维"],
      ja: ["三つのファイバーをそれぞれの中心へ収縮する", "三つのファイバーを再び広げる"]
    })[document.documentElement.lang] || ["Contract the three fibres to their centres", "Expand the three fibres again"];
    let contracted = false;
    function paint(t) {
      morphs.forEach(({node, from, to, template}) => {
        let i = 0;
        node.setAttribute("d", template.replace(numbers, () => {
          const n = i++;
          return String(from[n] + (to[n] - from[n]) * t);
        }));
      });
      points.forEach(({node, from, to}) => {
        node.setAttribute("cx", from[0] + (to[0] - from[0]) * t);
        node.setAttribute("cy", from[1] + (to[1] - from[1]) * t);
      });
      labels.forEach(({node, from, to}) => {
        node.style.left = (from + (to - from) * t) + "%";
        node.style.opacity = String(Math.max(0, 1 - t / .55));
        node.setAttribute("aria-hidden", String(t >= .55));
      });
      centreLabels.forEach(node => {
        node.style.opacity = t === 1 ? "1" : "0";
        node.setAttribute("aria-hidden", String(t !== 1));
      });
    }
    trigger.setAttribute("role", "button");
    trigger.setAttribute("aria-label", text[0]);
    trigger.setAttribute("aria-pressed", "false");
    trigger.tabIndex = 0;
    figure.classList.add("fiber-interactive");
    trigger.addEventListener("keydown", event => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        trigger.click();
      }
    });
    trigger.addEventListener("click", () => {
      if (figure.classList.contains("fiber-animating")) return;
      figure.classList.add("fiber-animating");
      trigger.setAttribute("aria-disabled", "true");
      let start;
      function frame(now) {
        if (start === undefined) start = now;
        const time = Math.min(1, (now - start) / 3600);
        const eased = time * time * (3 - 2 * time);
        paint(contracted ? 1 - eased : eased);
        if (time < 1) requestAnimationFrame(frame);
        else {
          contracted = !contracted;
          figure.classList.toggle("fiber-contracted", contracted);
          figure.classList.remove("fiber-animating");
          trigger.removeAttribute("aria-disabled");
          trigger.setAttribute("aria-pressed", String(contracted));
          trigger.setAttribute("aria-label", text[contracted ? 1 : 0]);
        }
      }
      requestAnimationFrame(frame);
    });
  });
})();

/* Expand the schematic family of paths into its type; paths become its points. */
(function () {
  "use strict";
  document.addEventListener("DOMContentLoaded", function () {
    const figure = document.getElementById("fig-coded-truth");
    if (!figure) return;
    const trigger = figure.querySelector(".coded-truth-trigger");
    const moving = figure.querySelector(".coded-truth-moving-space");
    const region = figure.querySelector(".coded-truth-region-copy");
    const targetSpace = figure.querySelector(".coded-truth-proof-target");
    if (!trigger || !moving || !region || !targetSpace) return;
    const targets = ["q", "r"].map(name => ({
      point: figure.querySelector(`.coded-truth-target-${name}`),
      copy: figure.querySelector(`.coded-truth-path-copy-${name}`)
    }));
    if (targets.some(target => !target.point || !target.copy)) return;
    const targetMarks = [...figure.querySelectorAll(".coded-truth-target")];
    const initialPath = region.getAttribute("d");
    const clamp = x => Math.max(0, Math.min(1, x));
    const smooth = x => { x = clamp(x); return x * x * (3 - 2 * x); };
    const arc = (t, control) => [100 + 210 * t, 95 + 2 * t * (1 - t) * (control - 95)];
    const source = Array.from({length: 64}, (_, i) =>
      i <= 32 ? arc(i / 32, 0) : arc((64 - i) / 32, 190));
    const labels = {
      en: "Unfold the highlighted path space",
      zh: "展开高亮的路径空间",
      ja: "強調されたパス空間を展開する"
    };
    trigger.setAttribute("role", "button");
    trigger.setAttribute("aria-label", labels[document.documentElement.lang] || labels.en);
    trigger.tabIndex = 0;
    figure.classList.add("coded-truth-interactive");
    trigger.addEventListener("keydown", function (event) {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        trigger.click();
      }
    });
    trigger.addEventListener("click", async function () {
      if (figure.classList.contains("coded-truth-playing")) return;
      trigger.setAttribute("aria-disabled", "true");
      figure.classList.add("coded-truth-playing");
      try {
        const matrix = moving.ownerSVGElement.getScreenCTM();
        if (!matrix) return;
        const inverse = matrix.inverse();
        const local = (x, y) => new DOMPoint(x, y).matrixTransform(inverse);
        const bounds = targetSpace.getBoundingClientRect();
        const topLeft = local(bounds.left, bounds.top);
        const bottomRight = local(bounds.right, bounds.bottom);
        const x = topLeft.x, y = topLeft.y, right = bottomRight.x, bottom = bottomRight.y;
        const middleY = (y + bottom) / 2;
        const radius = Math.min(8 / Math.hypot(matrix.a, matrix.b), (right - x) / 4, (bottom - y) / 4);
        const rectangle = `M${x} ${middleY} L${x} ${y + radius} Q${x} ${y} ${x + radius} ${y} ` +
          `L${right - radius} ${y} Q${right} ${y} ${right} ${y + radius} ` +
          `L${right} ${bottom - radius} Q${right} ${bottom} ${right - radius} ${bottom} ` +
          `L${x + radius} ${bottom} Q${x} ${bottom} ${x} ${bottom - radius} Z`;
        region.setAttribute("d", rectangle);
        const perimeter = region.getTotalLength();
        const destination = source.map((_, i) => region.getPointAtLength(perimeter * i / source.length));
        region.setAttribute("d", initialPath);
        const points = targets.map(target => {
          const box = target.point.getBoundingClientRect();
          return local(box.x + box.width / 2, box.y + box.height / 2);
        });
        await new Promise(resolve => {
          let started;
          function frame(now) {
            if (started === undefined) started = now;
            const time = clamp((now - started) / 4200);
            const progress = smooth((time - .1) / .72);
            const fade = 1 - smooth((time - .84) / .16);
            moving.style.opacity = String(smooth(time / .1));
            region.style.opacity = String(fade);
            region.setAttribute("d", source.map((point, i) =>
              `${i ? "L" : "M"}${point[0] + (destination[i].x - point[0]) * progress} ` +
              `${point[1] + (destination[i].y - point[1]) * progress}`).join(" ") + " Z");
            targets.forEach((target, i) => {
              const cx = 205 + (points[i].x - 205) * progress;
              const cy = 95 + (points[i].y - 95) * progress;
              target.copy.setAttribute("transform", `translate(${cx} ${cy}) scale(${1 - .98 * progress}) translate(-205 -95)`);
              target.copy.style.opacity = String(fade);
            });
            targetMarks.forEach(mark => { mark.style.opacity = String(1 - fade); });
            if (time < 1) requestAnimationFrame(frame);
            else resolve();
          }
          requestAnimationFrame(frame);
        });
      } finally {
        moving.style.opacity = "";
        region.style.opacity = "";
        region.setAttribute("d", initialPath);
        targets.forEach(target => {
          target.copy.removeAttribute("transform");
          target.copy.style.opacity = "";
        });
        targetMarks.forEach(mark => { mark.style.opacity = ""; });
        figure.classList.remove("coded-truth-playing");
        trigger.removeAttribute("aria-disabled");
      }
    });
  });
})();
