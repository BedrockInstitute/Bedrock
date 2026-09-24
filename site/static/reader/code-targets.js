/* Bedrock reader: code-targets. AGPL-3.0-only. */

  function definitionHoverTarget(target) {
    var candidate = target && target.closest && target.closest(
      "[data-hover-help], [data-hover-html], [data-hover-template], a[data-type], .type-node[data-expression-type], .expr-node, .Agda a[href]"
    );
    return candidate && !candidate.matches(".type-definition-link, .syntax-doc-link")
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

export { definitionHoverTarget, isDefinitionPopupAction, isUniverseTypeText };

    function hoverIdentity(name) {
      return name && name.getAttribute && (
        name.getAttribute("data-hover-help") || name.getAttribute("data-hover-template") || name.getAttribute("data-hover-html") ||
        name.getAttribute("data-expression-type") || name.getAttribute("data-type")
      );
    }

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
export { hoverIdentity, expressionAncestors, containingExpressionData, gestureIndex, gestureCandidates };
