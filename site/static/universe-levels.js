/* A presentation-only lens for known Agda universe operations. Original tokens,
   links, anchors and Unicode offsets remain in the DOM; the mathematical label
   is CSS-generated. The existing hover/modal engine displays the original code. */
(function () {
  "use strict";
  var operations = {"ℓ-zero": "zero", "lzero": "zero", "ℓ-suc": "suc", "lsuc": "suc", "ℓ-max": "max", "⊔": "join"};
  var containers = "pre.Agda, code.Agda, .Agda.inline-code, .single-line-code > code, .type-value.Agda";
  var excluded = ".universe-notation, [data-universe-raw], .appearance-preview, .Comment, .String, .Pragma, script, style, template";

  // Parse only this tiny, closed grammar, never infer a level from arbitrary ⊔/0/⁺.
  function parse(tokens, start, known, argument, levelAtom, atomOnly) {
    var node = parseAtom(tokens, start, known, argument, levelAtom);
    if (!node || atomOnly) return node;
    while (tokens[node.end] && tokens[node.end].text === "⊔" && known(node.end)) {
      var right = parse(tokens, node.end + 1, known, argument, levelAtom, true);
      if (!right) break;
      node = {op: "max", args: [node, right], start: start, end: right.end, changed: true};
    }
    return node;
  }
  function parseAtom(tokens, start, known, argument, levelAtom) {
    var token = tokens[start];
    if (!token) return null;
    var name = token.text;
    if (name === "(") {
      var inner = parse(tokens, start + 1, known, argument, levelAtom);
      if (!inner || !tokens[inner.end] || tokens[inner.end].text !== ")") return null;
      return {op: inner.op, args: inner.args, text: inner.text, start: start, end: inner.end + 1, changed: inner.changed};
    }
    var operation = Object.prototype.hasOwnProperty.call(operations, name) && known(start) && operations[name];
    if (operation === "zero") return {op: "atom", text: "0", start: start, end: start + 1, changed: true};
    if (operation && operation !== "join") {
      var first = parse(tokens, start + 1, known, true, levelAtom, true);
      if (!first) return null;
      var second = operation === "max" ? parse(tokens, first.end, known, true, levelAtom, true) : null;
      if (operation === "max" && !second) return null;
      return {op: operation, args: second ? [first, second] : [first], start: start,
        end: second ? second.end : first.end, changed: true};
    }
    if ((argument || levelAtom && levelAtom(start)) && !Object.prototype.hasOwnProperty.call(operations, name)
        && /^(?:[\p{L}\p{M}][\p{L}\p{M}\p{N}′″‴⁗'’₀-₉.-]*|_)$/u.test(name))
      return {op: "atom", text: name, start: start, end: start + 1, changed: false};
    return null;
  }
  function format(node) {
    if (node.op === "atom") return node.text;
    if (node.op === "max") return node.args.map(format).join(" ⊔ ");
    var child = node.args[0], value = format(child);
    return (child.op === "max" ? "(" + value + ")" : value) + "⁺";
  }
  function tokenize(text) {
    var result = [], pattern = /[^\s(){};]+|[(){};]/gu, match;
    while ((match = pattern.exec(text))) result.push({text: match[0], start: match.index, end: pattern.lastIndex});
    return result;
  }
  function textMap(scope) {
    var walker = document.createTreeWalker(scope, NodeFilter.SHOW_TEXT), nodes = [], text = "", node;
    while ((node = walker.nextNode())) { nodes.push({node: node, start: text.length, end: text.length + node.data.length}); text += node.data; }
    return {nodes: nodes, text: text};
  }
  // Book-wide notation convention, not type inference: ℓ and its numeric /
  // prime variants always denote levels, including prose and raw-code popups.
  // Do not match operator names (ℓ-max) or substrings of another identifier.
  function levelNamePattern() {
    return /(?<![\p{L}\p{M}\p{N}_′″‴⁗'’-])ℓ[\p{N}\p{M}′″‴⁗'’]*(?![\p{L}\p{M}\p{N}_′″‴⁗'’-])/gu;
  }
  function markConventionalLevels(scope) {
    var skip = '.universe-notation, .universe-source, .universe-parameter, script, style, template, textarea, input, select, [contenteditable], svg, math';
    if (scope.closest(skip)) return;
    var walker = document.createTreeWalker(scope, NodeFilter.SHOW_TEXT), nodes = [], node;
    while ((node = walker.nextNode())) {
      if (node.data.includes('ℓ') && !node.parentElement.closest(skip)) nodes.push(node);
    }
    nodes.forEach(function (text) {
      var matches = Array.from(text.data.matchAll(levelNamePattern()));
      matches.reverse().forEach(function (match) {
        var range = document.createRange(); range.setStart(text, match.index);
        range.setEnd(text, match.index + match[0].length);
        var span = document.createElement('span'); span.className = 'universe-parameter';
        span.dataset.universeLevel = 'true'; range.surroundContents(span);
      });
    });
  }
  function markCertifiedLevels(scope) {
    var selector = '[data-universe-level="true"]';
    var nodes = Array.from(scope.querySelectorAll(selector));
    if (scope.matches(selector)) nodes.unshift(scope);
    nodes.forEach(function (node) {
      if (!node.closest('.universe-notation, .universe-source, .appearance-preview')
          && !node.parentElement.closest('.universe-parameter')
          && !Object.prototype.hasOwnProperty.call(operations, node.textContent.trim()))
        node.classList.add('universe-parameter');
    });
  }
  function tokenElement(map, token) {
    var item = map.nodes.find(function (entry) { return token.start >= entry.start && token.start < entry.end; });
    return item && item.node.parentElement;
  }
  function knownOperator(map, tokens, index) {
    var token = tokens[index], element = tokenElement(map, token);
    if (!element || element.closest(excluded)) return false;
    var link = element.closest("a[href]");
    // Compiler/automatic-notation links certify the name; a same-spelled local
    // function, comment, string, or ordinary numeric/mixfix operator is untouched.
    if (!link && token.text === "⊔" && element.closest(".type-value")) return true;
    return !!(link && link.textContent.trim() === token.text
      && /(?:^|\/)(?:Base\.Prelude|Agda\.Primitive|Cubical\.Core\.Primitives|Cubical\.Foundations\.Prelude)(?:\.html)?#/.test(link.getAttribute("href"))
      && (link.matches(".Primitive, .Function, .Postulate, .inline-ref") || link.hasAttribute("data-name")));
  }
  var pageLevels = new Set();
  function collectPageLevels() {
    var names = new Map();
    document.querySelectorAll("pre.Agda a.Bound[data-type], pre.Agda a.Generalizable[data-type]").forEach(function (node) {
      var name = node.textContent.trim(), level = node.dataset.universeLevel === "true";
      names.set(name, (names.has(name) ? names.get(name) : true) && level);
    });
    names.forEach(function (level, name) { if (level) pageLevels.add(name); });
  }
  function markParameters(scope) {
    scope.querySelectorAll('[data-universe-level="true"]').forEach(function (node) {
      if (!node.closest(excluded) && !node.parentElement.closest('.universe-parameter') && !Object.prototype.hasOwnProperty.call(operations, node.textContent.trim()))
        node.classList.add("universe-parameter");
    });
    if (scope.closest(excluded)) return;
    var map = textMap(scope), tokens = tokenize(map.text), stack = [], closes = new Map(), parents = new Map(), binders = [];
    tokens.forEach(function (token, index) {
      if (token.text === "(" || token.text === "{") { parents.set(index, stack[stack.length - 1]); stack.push(index); }
      if (token.text === ")" || token.text === "}") { var open = stack.pop(); if (open !== undefined) closes.set(open, index); }
    });
    closes.forEach(function (close, open) {
      var colon = open + 1;
      while (colon < close && /^[\p{L}\p{M}][\p{L}\p{M}\p{N}′'₀-₉.-]*$/u.test(tokens[colon].text)) colon++;
      if (colon === open + 1 || !tokens[colon] || tokens[colon].text !== ":") return;
      var typeToken = tokens[colon + 1], typeElement = typeToken && tokenElement(map, typeToken);
      var typeLink = typeElement && typeElement.closest('a[href]');
      var level = colon + 2 === close && typeToken.text === "Level" && typeLink
        && /(?:Base\.Prelude|Agda\.Primitive|Cubical\.Core\.Primitives)(?:\.html)?#/.test(typeLink.getAttribute("href"));
      binders.push({start: open + 1, end: closes.get(parents.get(open)) || tokens.length,
        names: new Set(tokens.slice(open + 1, colon).map(function (token) { return token.text; })), level: Boolean(level)});
    });
    binders.sort(function (a, b) { return b.start - a.start; });
    var inferred = [];
    tokens.forEach(function (token, index) {
      var element = tokenElement(map, token);
      if (!element || element.closest(excluded + ", a, .universe-parameter, [data-hover-help]")) return;
      var binder = binders.find(function (entry) { return index >= entry.start && index < entry.end && entry.names.has(token.text); });
      var level = binder ? binder.level : !scope.closest(".type-value") && pageLevels.has(token.text);
      if (!level) return;
      var item = map.nodes.find(function (entry) { return token.start >= entry.start && token.end <= entry.end; });
      if (item) inferred.push({item: item, token: token});
    });
    inferred.reverse().forEach(function (entry) {
      var range = document.createRange(); range.setStart(entry.item.node, entry.token.start - entry.item.start);
      range.setEnd(entry.item.node, entry.token.end - entry.item.start);
      var span = document.createElement("span"); span.className = "universe-parameter"; span.dataset.universeLevel = "true";
      range.surroundContents(span);
    });
  }
  function sourceMarkup(fragment) {
    var holder = document.createElement("span"); holder.setAttribute("data-universe-raw", "");
    holder.appendChild(fragment.cloneNode(true));
    var moduleName = (window.bedrock || {}).chapter || (window.bedrock || {}).module || "";
    holder.querySelectorAll("[id]").forEach(function (node) { node.removeAttribute("id"); });
    holder.querySelectorAll(".expr-node").forEach(function (node) {
      node.classList.replace("expr-node", "type-node");
      if (moduleName && node.dataset.exprId) node.dataset.expressionType = moduleName + "#" + node.dataset.exprId;
    });
    // Rebase *all* structural ranges to the extracted fragment's Unicode text.
    holder.querySelectorAll(".type-node").forEach(function (node) {
      var before = document.createRange(); before.setStart(holder, 0); before.setEndBefore(node);
      var start = Array.from(before.toString()).length;
      node.dataset.exprStart = String(start); node.dataset.exprEnd = String(start + Array.from(node.textContent).length);
      node.classList.remove("expr-active", "type-active");
    });
    holder.querySelectorAll(".occ, .name-active").forEach(function (node) { node.classList.remove("occ", "name-active"); });
    holder.querySelectorAll(".universe-parameter").forEach(function (node) { node.classList.remove("universe-parameter"); });
    return holder.outerHTML;
  }
  function badge(source, label) {
    var element = document.createElement("span"); element.className = "universe-notation";
    element.dataset.levelMath = label;
    element.dataset.hoverHtml = sourceMarkup(source);
    element.setAttribute("role", "button"); element.setAttribute("tabindex", "0");
    element.setAttribute("aria-haspopup", "dialog"); element.setAttribute("aria-expanded", "false");
    var copy = {zh: "宇宙层级：{level}。展开原始 Agda 代码", ja: "宇宙レベル：{level}。元の Agda コードを表示", en: "Universe level: {level}. Show original Agda code"};
    element.setAttribute("aria-label", (copy[document.documentElement.lang] || copy.en).replace("{level}", label));
    var original = document.createElement("span"); original.className = "universe-source";
    original.setAttribute("aria-hidden", "true"); original.setAttribute("inert", "");
    original.appendChild(source); element.appendChild(original); return element;
  }
  function decorate(scope) {
    if (scope.closest(excluded)) return;
    markParameters(scope);
    var map = textMap(scope);
    if (!/ℓ-(?:zero|suc|max)|\bl(?:zero|suc)\b|⊔/.test(map.text)) return;
    var tokens = tokenize(map.text), matches = [], importNames = new Set();
    tokens.forEach(function (token, index) {
      if (!/^(?:using|hiding|renaming)$/.test(token.text) || !tokens[index + 1] || tokens[index + 1].text !== "(") return;
      var depth = 0;
      for (var cursor = index + 1; cursor < tokens.length; cursor++) {
        importNames.add(cursor);
        if (tokens[cursor].text === "(") depth++;
        if (tokens[cursor].text === ")" && --depth === 0) break;
      }
    });
    for (var i = 0; i < tokens.length; i++) {
      if (importNames.has(i)) continue;
      var levelAtom = function (index) {
        var element = tokenElement(map, tokens[index]);
        return !!(element && !element.closest(excluded) && element.closest('[data-universe-level="true"]'));
      };
      if (tokens[i].text !== "(" && !Object.prototype.hasOwnProperty.call(operations, tokens[i].text) && !levelAtom(i)) continue;
      var expression = parse(tokens, i, function (index) { return knownOperator(map, tokens, index); }, false, levelAtom);
      if (!expression || !expression.changed) continue;
      var begin = tokens[i].start, end = tokens[expression.end - 1].end;
      var first = tokenElement(map, tokens[i]), last = tokenElement(map, tokens[expression.end - 1]);
      if (!first || !last || first.closest(excluded) || last.closest(excluded)) continue;
      // A bare name in an import/renaming/declaration is not a level expression.
      var line = map.text.slice(map.text.lastIndexOf("\n", begin - 1) + 1, begin);
      if (/(?:\busing|\bhiding|\brenaming|\bimport|\bBUILTIN)\b/.test(line)
          || tokens[expression.end] && /^(?:;|:|to)$/.test(tokens[expression.end].text)) continue;
      // Source layout is significant; never collapse a multi-line expression.
      if (map.text.slice(begin, end).includes("\n")) continue;
      matches.push({start: begin, end: end, label: format(expression)}); i = expression.end - 1;
    }
    // Work backwards so earlier source offsets and nodes remain valid.
    matches.reverse().forEach(function (match) {
      var start = map.nodes.find(function (entry) { return match.start >= entry.start && match.start < entry.end; });
      var end = map.nodes.find(function (entry) { return match.end > entry.start && match.end <= entry.end; });
      if (!start || !end || !start.node.isConnected || !end.node.isConnected) return;
      var range = document.createRange();
      range.setStart(start.node, match.start - start.start); range.setEnd(end.node, match.end - end.start);
      var boundary = range.commonAncestorContainer;
      if (boundary.nodeType === Node.TEXT_NODE) boundary = boundary.parentNode;
      if (range.toString() === boundary.textContent) boundary = boundary.parentNode;
      // Lift exact endpoints out of complete token/AST wrappers. This avoids
      // splitting anchors and preserves complete compiler nodes where possible.
      var startNode = range.startContainer, startOffset = range.startOffset;
      while (startOffset === 0 && startNode !== scope && startNode.parentNode !== scope && startNode.parentNode !== boundary && !startNode.previousSibling) {
        startNode = startNode.parentNode; startOffset = 0;
      }
      if (startOffset === 0 && startNode !== scope) range.setStartBefore(startNode);
      var endNode = range.endContainer, endOffset = range.endOffset;
      while (endNode !== scope && endNode.parentNode !== scope && endNode.parentNode !== boundary && !endNode.nextSibling
          && endOffset === (endNode.nodeType === Node.TEXT_NODE ? endNode.length : endNode.childNodes.length)) {
        endNode = endNode.parentNode; endOffset = endNode.childNodes.length;
      }
      if (endNode !== scope && endOffset === (endNode.nodeType === Node.TEXT_NODE ? endNode.length : endNode.childNodes.length)) range.setEndAfter(endNode);
      // Never partially extract a compiler range: partial wrappers would create
      // duplicate AST identities. Keep the outer parentheses if necessary.
      var fragment = range.cloneContents();
      var partial = Array.from(fragment.querySelectorAll(".expr-node, .type-node")).some(function (node) {
        var key = node.dataset.exprId || node.dataset.expressionType;
        var original = Array.from(scope.querySelectorAll(".expr-node, .type-node")).find(function (candidate) {
          return (candidate.dataset.exprId || candidate.dataset.expressionType) === key;
        });
        return original && node.textContent !== original.textContent;
      });
      if (partial) return;
      var source = range.extractContents(); range.insertNode(badge(source, match.label));
    });
  }
  function scan(scope) {
    if (!scope || scope.nodeType !== Node.ELEMENT_NODE) return;
    markCertifiedLevels(scope);
    markConventionalLevels(scope);
    if (scope.closest(excluded)) return;
    var parent = scope.closest(containers);
    if (parent) decorate(parent);
    scope.querySelectorAll(containers).forEach(function (node) {
      if (!node.parentElement.closest(containers)) decorate(node);
    });
  }
  window.bedrockUniverseLevels = {scan: scan};
  document.addEventListener("DOMContentLoaded", function () {
    collectPageLevels();
    scan(document.body);
    new MutationObserver(function (records) {
      var scopes = new Set();
      records.forEach(function (record) {
        if (record.type === "characterData") scopes.add(record.target.parentElement);
        else record.addedNodes.forEach(function (node) {
          if (node.nodeType === Node.ELEMENT_NODE) scopes.add(node);
          else if (node.nodeType === Node.TEXT_NODE && node.parentElement) scopes.add(node.parentElement);
        });
      });
      scopes.forEach(scan);
    }).observe(document.body, {childList: true, subtree: true, characterData: true});
  });
})();
