/* Bedrock reader: disclosure. AGPL-3.0-only. */

  /* Keep the Agda module declaration visible while its body folds as one unit. */
  function initSubmoduleFolds() {
    document.querySelectorAll("details.submodule-fold").forEach(function (details) {
      var heading = details.querySelector(":scope > summary.submodule-fold-heading");
      var content = details.querySelector(":scope > .submodule-fold-content");
      enhanceDisclosure(details, heading, content, 260, "submodule-closing");
    });
  }

  /* Shared by source submodules and the dynamically loaded learning route. */
  function enhanceDisclosure(details, heading, content, duration, closingClass) {
      if (!heading || !content) return;
      var expanded = details.open;
      var animation = null;
      closingClass = closingClass || "disclosure-closing";
      details.dataset.foldExpanded = String(expanded);
      details.addEventListener("toggle", function () {
        if (!animation) {
          expanded = details.open;
          details.dataset.foldExpanded = String(expanded);
        }
      });
      heading.addEventListener("click", function (event) {
        if (event.target.closest("a, button, input, select, textarea")) {
          event.stopPropagation();
          return;
        }
        if (!content.animate || window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
          if (animation) {
            animation.cancel(); animation = null;
            content.style.height = ""; content.style.overflow = "";
            details.classList.remove(closingClass);
          }
          expanded = !details.open;
          details.dataset.foldExpanded = String(expanded);
          return;
        }
        event.preventDefault();
        var startHeight = details.open ? content.getBoundingClientRect().height : 0;
        var startOpacity = details.open ? parseFloat(getComputedStyle(content).opacity) : 0;
        if (animation) animation.cancel();
        expanded = !expanded;
        details.dataset.foldExpanded = String(expanded);
        details.open = true;
        content.style.height = startHeight + "px";
        content.style.overflow = "hidden";
        details.classList.toggle(closingClass, !expanded);
        var endHeight = expanded ? content.scrollHeight : 0;
        var motion = content.animate([
          { height: startHeight + "px", opacity: startOpacity },
          { height: endHeight + "px", opacity: expanded ? 1 : 0 }
        ], { duration: duration, easing: "cubic-bezier(.2,.75,.25,1)", fill: "forwards" });
        animation = motion;
        motion.onfinish = function () {
          if (animation !== motion) return;
          details.open = expanded;
          motion.cancel();
          animation = null;
          content.style.height = "";
          content.style.overflow = "";
          details.classList.remove(closingClass);
        };
      });
  }

export { initSubmoduleFolds, enhanceDisclosure };
