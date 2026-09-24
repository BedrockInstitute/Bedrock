/* Bedrock reader: notes. AGPL-3.0-only. */
import { cfg } from "./document.js";

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

export { initCodeNotes, collectProseNotes, positionMarginNotes };
