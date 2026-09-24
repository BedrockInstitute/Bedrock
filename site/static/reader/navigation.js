import { readPreference, writePreference } from './preferences.js';
/* Bedrock reader: navigation. AGPL-3.0-only. */
import { cfg, isDefinitionModalDocument, modalReadingScroller } from "./document.js";

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
      if (readPreference("toc-collapsed") === "true") body.classList.add("nav-collapsed");
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
      try { writePreference("toc-collapsed", collapsed ? "true" : "false"); } catch (_) {}
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


export { initPageScroll, initHeaderOffset, updateAnchorInset, initMobileSearchScroll, sectionOutline, initSectionTracking, initNav };
