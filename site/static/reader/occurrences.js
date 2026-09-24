/* Bedrock reader: occurrences. AGPL-3.0-only. */
import { compactPointer } from "./document.js";

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
        ".Agda a[href]"
      );
      return link && !link.hasAttribute("data-hover-stop") ? link : null;
    }
    function set(key, on) {
      document.querySelectorAll(
        ".Agda a[href]"
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

export { initOccur };
