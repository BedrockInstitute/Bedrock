/* Bedrock reader: glyphs. AGPL-3.0-only. */

  /* One text-only pass for page code, inline prose and all dynamic hover/modal
     content. Do not replace markup, source text, links or Agda range offsets. */
  function decorateDottedOperators(scope) {
    var excluded = ".dotted-operator, script, style, textarea, input, select, " +
      "svg, math, .math, .katex, [contenteditable]";
    function decorateText(node) {
      if (!/[⇒¬]\u0307/u.test(node.data) || !node.parentElement ||
          node.parentElement.closest(excluded)) return;
      var text = node.data, pattern = /[⇒¬]\u0307(?!\p{M})/gu, match, offset = 0;
      var fragment = document.createDocumentFragment();
      while ((match = pattern.exec(text))) {
        fragment.appendChild(document.createTextNode(text.slice(offset, match.index)));
        var span = document.createElement("span");
        span.className = "dotted-operator";
        span.textContent = match[0];
        fragment.appendChild(span);
        offset = pattern.lastIndex;
      }
      if (!offset) return;
      fragment.appendChild(document.createTextNode(text.slice(offset)));
      node.replaceWith(fragment);
    }
    if (scope.nodeType === Node.TEXT_NODE) { decorateText(scope); return; }
    if (scope.nodeType !== Node.ELEMENT_NODE || scope.closest(excluded)) return;
    var walker = document.createTreeWalker(scope, NodeFilter.SHOW_TEXT);
    var texts = [], current;
    while ((current = walker.nextNode())) texts.push(current);
    texts.forEach(decorateText);
  }
  decorateDottedOperators(document.body);
  new MutationObserver(function (records) {
    records.forEach(function (record) {
      if (record.type === "characterData") decorateDottedOperators(record.target);
      else record.addedNodes.forEach(decorateDottedOperators);
    });
  }).observe(document.body, {childList: true, subtree: true, characterData: true});
