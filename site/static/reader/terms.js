/* Bedrock reader: terms. AGPL-3.0-only. */
import { cfg } from "./document.js";

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

export { initTermHover };
