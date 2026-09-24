import { hoverIdentity, expressionAncestors, containingExpressionData, gestureIndex, gestureCandidates } from "./code-targets.js";
/* Bedrock reader: hover. AGPL-3.0-only. */
import { cfg, compactPointer, modalReadingScroller } from "./document.js";
import { definitionHoverTarget, isUniverseTypeText } from "./code-targets.js";
import { createTypeStore } from "./type-store.js";
import { HoverBranch } from "./hover-branch.js";
import { positionBelow, clearCodeSelection } from './hover-view.js';

  function initHover() {
    const types = createTypeStore(cfg);
    const fetchTypes = types.get;
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
    function definitionAction(href, name, isModule) {
      var link = document.createElement("a");
      link.className = "type-definition-link";
      link.href = href;
      if (name) link.setAttribute("data-name", name);
      if (isModule) link.setAttribute("data-module-target", "true");
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
    function scheduleHoverClose(callback) {
      return branch.schedule(callback);
    }
    var branch = new HoverBranch({
      persistent: () => compactPointer.matches,
      entered: cancelHide,
      left: () => { if (!popup.hidden) laterHide(); },
      dispose: entry => {
        nameRequest += 1;
        entry.popup.remove();
        if (entry.activeName) entry.activeName.classList.remove("name-active");
        if (entry.activeNode) entry.activeNode.classList.remove("type-active");
        entry.anchor.classList.remove("info-active");
        entry.anchor.setAttribute("aria-expanded", "false");
        if (entry.popup === rangeScope) setRangeScope(fallbackRangeScope());
      }
    });
    var namePopups = branch.entries, nameRequest = 0;
    var leafActiveName = null;
    function clearLeafNameHighlight() {
      if (leafActiveName) leafActiveName.classList.remove("name-active");
      leafActiveName = null;
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
      branch.removeFrom(index);
    }
    function hideName() {
      clearLeafNameHighlight();
      if (namePopups.length) removeNamePopupsFrom(0);
      else nameRequest += 1;
    }
    function cancelNameClose(entry) {
      branch.enter(entry);
    }
    function nameBranchHovered(entry) {
      return branch.hovered(entry);
    }
    function laterHideName(entry) {
      branch.leave(entry);
    }
    function positionNameEntry(entry) {
      positionBelow(entry.popup, entry.anchor);
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
      types.resolve(name).then(function (payload) {
        var { html, infoHTML, helpKey, template, hasDefinition, hasChapterModal } = payload;
        if (serial !== nameRequest || !name.isConnected
            || (parent && namePopups.indexOf(parent) < 0)
            || (!compactPointer.matches && name.matches && !name.matches(":hover") && document.activeElement !== name)
            || (!html && !(compactPointer.matches && hasDefinition))) return;
        removeNamePopupsFrom(parentIndex + 1);
        var namePopup = document.createElement("div");
        namePopup.className = "hover-popup name-hover-popup Agda";
        if (infoHTML || helpKey) {
          namePopup.classList.add("info-hover-popup");
          if ((template && template.hasAttribute("data-boilerplate-module")) || name.classList.contains("universe-notation"))
            namePopup.classList.add("boilerplate-hover-popup");
          name.classList.add("info-active");
          name.setAttribute("aria-expanded", "true");
        }
        namePopup.setAttribute("role", "dialog");
        namePopup.dataset.hoverDepth = String(parentIndex + 1);
        if (hasDefinition) namePopup.classList.add("has-definition-link");
        if (hasChapterModal) namePopup.classList.add("has-definition-link");
        var nameValue = document.createElement("div");
        nameValue.className = "type-value Agda";
        if (html) nameValue.innerHTML = html;
        else nameValue.textContent = name.textContent.trim();
        markTerminalHoverStops(nameValue, identity);
        if (isUniverseTypeText(nameValue.textContent))
          namePopup.classList.add("hover-terminal");
        if (name.classList.contains("universe-notation")) {
          var sourceLabel = document.createElement("div");
          sourceLabel.className = "source-hover-label";
          sourceLabel.textContent = {en: "Universe level · Original Agda", zh: "宇宙层级 · 原始 Agda", ja: "宇宙レベル · 元の Agda"}[cfg.lang] || "Universe level · Original Agda";
          namePopup.appendChild(sourceLabel);
        }
        namePopup.appendChild(nameValue);
        if (hasDefinition) namePopup.appendChild(definitionAction(name.href,
          name.getAttribute("data-name") || name.textContent.trim(), name.classList.contains("Module")));
        if (hasChapterModal) namePopup.appendChild(definitionAction(name.href,
          name.getAttribute("data-name") || name.textContent.trim(), true));
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
        branch.append(entry);
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
      return !(target.closest && target.closest("[data-hover-help], [data-hover-html], [data-hover-template]"))
        && expressionAncestors(target).length > 0;
    }
    function clearHighlight(scope) {
      leafActiveName = null;
      clearCodeSelection(scope || document);
    }
    function position() {
      if (popup.hidden || !anchor) return;
      positionBelow(popup, anchor);
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
      hideTimer = scheduleHoverClose(function () {
        if ((anchor && anchor.matches(":hover")) || popup.matches(":hover")
            || (namePopups.length && nameBranchHovered(namePopups[0]))) return;
        hide();
      });
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
      if (event.target.closest && event.target.closest("[data-hover-help], [data-hover-html], [data-hover-template]")) return;
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
        var info = event.target.closest && event.target.closest("[data-hover-help], [data-hover-html], [data-hover-template]");
        if (info) {
          event.preventDefault(); event.stopPropagation(); showName(info); return;
        }
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
            "[data-hover-help], [data-hover-html], [data-hover-template], a[href], a[data-type], .type-node[data-expression-type]"
          ))) return;
      if (!target) {
        pinned = false; hide(); hideName();
        return;
      }
      if (usesInspector(event.target)) {
        return;
      } else if (target.matches("[data-hover-help], [data-hover-html], [data-hover-template], a[href], .type-node[data-expression-type]")) {
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
        "[data-hover-help], [data-hover-html], [data-hover-template], a[data-type], .type-node[data-expression-type]"
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
        "[data-hover-help], [data-hover-html], [data-hover-template], a[data-type], .type-node[data-expression-type]"
      );
      if (name && !usesInspector(event.target)
          && (!event.relatedTarget || (!name.contains(event.relatedTarget)
              && !namePopupContains(event.relatedTarget)))) {
        var child = namePopups.find(function (entry) { return entry.anchor === name; });
        laterHideName(child);
      }
    });
    document.addEventListener("focusin", function (event) {
      var info = event.target.closest && event.target.closest("[data-hover-help], [data-hover-html], [data-hover-template]");
      if (info) showName(info);
    });
    document.addEventListener("focusout", function (event) {
      var entry = namePopups.find(function (item) { return item.anchor === event.target; });
      if (entry) laterHideName(entry);
    });
    document.addEventListener("keydown", function (event) {
      if ((event.key === "Enter" || event.key === " ") && event.target.matches("[data-hover-help], [data-hover-html], [data-hover-template]")) {
        if (!compactPointer.matches && event.key === "Enter"
            && event.target.matches('a[href][data-hover-navigate="modal"]')) return;
        event.preventDefault(); showName(event.target);
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

export { initHover };
