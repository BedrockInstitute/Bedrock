/* Ask an assistant about a passage of this book.
 *
 * Select prose or Agda anywhere in a chapter and a trigger appears beside the selection.
 * It opens a dialog holding one plain-text handover document: what was selected, where
 * exactly it sits, what the textbook covers, and which of this site's machine-readable resources
 * an assistant should fetch before answering. The reader copies that text into whatever
 * assistant they already use. Nothing is sent anywhere from this page: there is no API
 * key, no network call, and no third party in the loop.
 *
 * Vanilla JS, no build step. AGPL-3.0-only, like the rest of this front end.
 */
(function () {
  "use strict";
  var cfg = window.bedrock || {};
  var lang = cfg.lang || "en";

  /* ---- wording ------------------------------------------------------------- */
  /* The handover is written in the language of the page the reader is on, because the
     reader reads it before they paste it, and because it ends by asking for an answer
     in that language. Only the labels differ between the three; the structure of the
     document is identical, so an assistant sees the same fields whatever the edition. */
  var STRINGS = {
    en: {
      colon: ": ", quoteOpen: '"', quoteClose: '"',
      trigger: "Ask AI", triggerTitle: "Build a handover text about this selection (Alt+A)",
      dialogTitle: "Handover text for your assistant",
      hint: "Click anywhere in the text to copy it, then paste it into your own assistant. "
          + "Nothing leaves this page.",
      copy: "Copy", close: "Close", regionLabel: "Handover text, click to copy",
      idle: "Not copied yet.", copied: "Copied to the clipboard.",
      failed: "The browser refused clipboard access. Select the text and copy it by hand.",


      hSelection: "The passage I selected",
      hWhere: "Where the passage is",

      hFetch: "How to get the rest of the context",
      hWant: "What I want from you",
      fPage: "Page", fMarkdown: "The same page as Markdown, smaller and easier to read",
      fCanonical: "Canonical address of this page",
      fChapter: "Chapter", fStage: "Learning stage", fModule: "Agda module",
      fSection: "Section it falls under", fBlock: "Anchor of the block I selected",
      fSpans: "My selection runs on past that block, as far as",
      fBefore: "The text immediately before my selection",
      fAfter: "The text immediately after my selection",
      fCode: "I selected part of a displayed Agda code block.",
      fDefinition: "The Agda definition my selection sits in",
      fToken: "Anchor of the nearest Agda token at or before my selection",
      fLinks: "Identifiers and terms linked inside my selection",
      fSource: "The Agda master this chapter is generated from",
      fPrereq: "Chapters this one depends on",

      fReadingOrder: "Position in the reading order",
      position: function (order, total) { return "chapter " + order + " of " + total; },
      fetch: function (origin, mdNote) {
        return [
          "`" + origin + "/llms.txt`: the guide this site publishes for AI agents. It lists"
          + " every chapter and every machine-readable endpoint. Read it first.",
          mdNote,
          "`" + origin + "/" + lang + "/reading-routes.json`: the chapter graph, with each"
          + " chapter's title, learning stage, prerequisites and reading routes.",
          "`" + origin + "/" + lang + "/terms.json`: the glossary, with a one-sentence recap"
          + " of each term and the chapter that introduces it.",
          "`" + origin + "/" + lang + "/search.json`: every Agda identifier the book defines,"
          + " with its module, its anchor and its type.",
          "`" + origin + "/" + lang + "/types/<Module>.json`: the elaborated type of every"
          + " token of a chapter, keyed by the anchor that token carries in the page URL.",
          "`" + (cfg.repository || "") + "`: the repository, if you want the raw sources."
        ];
      },
      mdNote: function (url) {
        return "`" + url + "`: this exact page as plain Markdown. Prefer it over the HTML:"
             + " same prose, same Agda, a fraction of the size.";
      },
      mdRule: "Appending `.md` to any chapter URL on this site gives that chapter as plain"
            + " Markdown."
    },
    zh: {
      colon: "：", quoteOpen: "「", quoteClose: "」",
      trigger: "问 AI", triggerTitle: "为这段选中内容生成交接文（Alt+A）",
      dialogTitle: "交给你的 AI 的交接文",
      hint: "点击文字任何位置即可复制，然后粘贴到你自己的 AI 对话里。本页不会向任何地方发送数据。",
      copy: "复制", close: "关闭", regionLabel: "交接文，点击复制",
      idle: "尚未复制。", copied: "已复制到剪贴板。",
      failed: "浏览器拒绝了剪贴板访问。请手动选中文字复制。",


      hSelection: "我选中的内容",
      hWhere: "这段内容的位置",

      hFetch: "如何获取其余上下文",
      hWant: "我希望你做什么",
      fPage: "页面", fMarkdown: "同一页面的 Markdown 版本，体积更小也更易读",
      fCanonical: "本页的规范地址",
      fChapter: "章", fStage: "学习阶段", fModule: "Agda 模块",
      fSection: "所属小节", fBlock: "我选中的段落锚点",
      fSpans: "我的选区越过了该段落，一直延伸到",
      fBefore: "紧接在选区之前的文字",
      fAfter: "紧接在选区之后的文字",
      fCode: "我选中的是展示的 Agda 代码块的一部分。",
      fDefinition: "选区所处的 Agda 定义",
      fToken: "选区处或之前最近的 Agda 记号锚点",
      fLinks: "选区内带链接的标识符与术语",
      fSource: "生成本章的 Agda 母本",
      fPrereq: "本章依赖的章节",

      fReadingOrder: "在阅读顺序中的位置",
      position: function (order, total) { return "第 " + order + " 章，全书共 " + total + " 章"; },
      fetch: function (origin, mdNote) {
        return [
          "`" + origin + "/llms.txt`：本站为 AI 发布的说明，列出了全部章节与全部机器可读端点。请先读它。",
          mdNote,
          "`" + origin + "/" + lang + "/reading-routes.json`：章节依赖图，含每章的标题、学习阶段、"
          + "先修与阅读路线。",
          "`" + origin + "/" + lang + "/terms.json`：术语表，含每个术语的一句话回顾与引入它的章节。",
          "`" + origin + "/" + lang + "/search.json`：本书定义的全部 Agda 标识符，含模块、锚点与类型。",
          "`" + origin + "/" + lang + "/types/<Module>.json`：一章中每个记号的展开类型，"
          + "以该记号在页面 URL 中的锚点为键。",
          "`" + (cfg.repository || "") + "`：源码仓库，如果你需要原始文件。"
        ];
      },
      mdNote: function (url) {
        return "`" + url + "`：就是本页的纯 Markdown 版本。请优先读它：散文与 Agda 都一样，体积只有一小部分。";
      },
      mdRule: "在本站任何章节 URL 后面加上 `.md`，就能得到该章的纯 Markdown 版本。"
    },
    ja: {
      colon: "：", quoteOpen: "「", quoteClose: "」",
      trigger: "AI に質問", triggerTitle: "この選択範囲について引き継ぎ文を作る（Alt+A）",
      dialogTitle: "お使いの AI に渡す引き継ぎ文",
      hint: "文字のどこをクリックしてもコピーできます。ご自分の AI との対話に貼り付けてください。"
          + "このページから外部へ送信されるものはありません。",
      copy: "コピー", close: "閉じる", regionLabel: "引き継ぎ文、クリックでコピー",
      idle: "まだコピーしていません。", copied: "クリップボードにコピーしました。",
      failed: "ブラウザがクリップボードへのアクセスを拒否しました。手動で選択してコピーしてください。",


      hSelection: "選択した一節",
      hWhere: "その位置",

      hFetch: "残りの文脈を得る方法",
      hWant: "お願いしたいこと",
      fPage: "ページ", fMarkdown: "同じページの Markdown 版。小さくて読みやすい",
      fCanonical: "このページの正規アドレス",
      fChapter: "章", fStage: "学習段階", fModule: "Agda モジュール",
      fSection: "属する節", fBlock: "選択した段落のアンカー",
      fSpans: "選択範囲はその段落を越えて次まで続いています",
      fBefore: "選択範囲の直前の文",
      fAfter: "選択範囲の直後の文",
      fCode: "表示された Agda コードブロックの一部を選択しました。",
      fDefinition: "選択範囲が属する Agda の定義",
      fToken: "選択範囲またはその直前で最も近い Agda トークンのアンカー",
      fLinks: "選択範囲内でリンクされている識別子と用語",
      fSource: "この章を生成している Agda の原本",
      fPrereq: "この章が依存する章",

      fReadingOrder: "読書順での位置",
      position: function (order, total) { return "第 " + order + " 章（全 " + total + " 章）"; },
      fetch: function (origin, mdNote) {
        return [
          "`" + origin + "/llms.txt`：本サイトが AI エージェント向けに公開している案内です。"
          + "全章と全ての機械可読エンドポイントが載っています。まずこれを読んでください。",
          mdNote,
          "`" + origin + "/" + lang + "/reading-routes.json`：章の依存グラフ。各章の題、学習段階、"
          + "前提、読書ルートを含みます。",
          "`" + origin + "/" + lang + "/terms.json`：用語集。各用語の一文の要約と、"
          + "それを導入する章を含みます。",
          "`" + origin + "/" + lang + "/search.json`：本書が定義する全ての Agda 識別子。"
          + "モジュール、アンカー、型を含みます。",
          "`" + origin + "/" + lang + "/types/<Module>.json`：ある章の各トークンの展開された型。"
          + "ページ URL でそのトークンが持つアンカーがキーです。",
          "`" + (cfg.repository || "") + "`：原典が必要な場合のリポジトリです。"
        ];
      },
      mdNote: function (url) {
        return "`" + url + "`：まさにこのページの純 Markdown 版です。HTML よりこちらを優先してください。"
             + "文章も Agda も同じで、大きさはごく一部です。";
      },
      mdRule: "本サイトのどの章の URL にも `.md` を付ければ、その章の純 Markdown 版が得られます。"
    }
  };
  var generic = {
    en: {docTitle: `Explain a passage of ${cfg.site || 'this textbook'}`, intro: 'Explain the selected passage using the linked sources.', hProject: 'About this textbook', fLibrary: 'This is a referenced library module, not a chapter.', project: [cfg.description || ''], want: ['Explain the selection and its prerequisites. Follow the cited sources instead of guessing. Answer in English.']},
    zh: {docTitle: `请解释 ${cfg.site || '教科书'} 中的一段内容`, intro: '请根据所链接的资料解释选中的段落。', hProject: '关于本教科书', fLibrary: '这是供查阅的库模块，并非本书章节。', project: [cfg.description || ''], want: ['解释选段及其先修知识，请查阅资料而非猜测。请用中文回答。']},
    ja: {docTitle: `${cfg.site || '教科書'} の一節を説明してください`, intro: 'リンク先の資料を使って選択した一節を説明してください。', hProject: 'この教科書について', fLibrary: '参照用のライブラリモジュールであり、本書の章ではありません。', project: [cfg.description || ''], want: ['選択した一節と前提知識を説明してください。推測せず資料を参照し、日本語で答えてください。']}
  };
  var S = Object.assign({}, STRINGS[lang] || STRINGS.en, generic[lang] || generic.en, cfg.agentCopy || {});

  /* ---- where the reader is, as an address an agent can fetch --------------- */

  function isLocal() {
    return !location.host || /^(localhost|127\.|0\.0\.0\.0|\[::1\])/.test(location.host);
  }
  /* On a local preview or a mirror deployment the address in the bar is not fetchable
     by anyone else, so the handover quotes the canonical URL the renderer stamped in. */
  function pageUrl() {
    if (isLocal() && cfg.canonical) return cfg.canonical;
    return location.origin + location.pathname;
  }
  function originUrl() {
    var url = pageUrl();
    var cut = url.indexOf("/" + lang + "/");
    return cut > 0 ? url.slice(0, cut) : url.replace(/\/[^/]*$/, "");
  }
  function markdownUrl() {
    if (!cfg.markdown) return "";
    return pageUrl().replace(/[^/]*$/, cfg.markdown);
  }

  /* ---- locating the selection --------------------------------------------- */

  var BLOCK_ID = /^p-\d+$/;

  function elementOf(node) {
    return node && node.nodeType === 1 ? node : node && node.parentElement;
  }

  function article() { return document.querySelector("main article"); }

  /* The addressable block containing a point: the paragraph, list item, block quote or
     table the renderer numbered, or else the code block or heading it fell in. */
  function blockOf(node) {
    var el = elementOf(node);
    var root = article();
    while (el && el !== root) {
      if (el.id && BLOCK_ID.test(el.id)) return el;
      if (el.tagName === "PRE" || /^H[1-6]$/.test(el.tagName)) return el;
      el = el.parentElement;
    }
    return null;
  }

  var HEADING_ID = /^sec-\d+$/;
  var ANCHORED_HEADING = "h1[id],h2[id],h3[id],h4[id],h5[id],h6[id]";

  /* The nearest heading above a point that the renderer gave an anchor. Requiring the
     anchor is what keeps the route explorer out: its headings are built in the browser
     and carry no id, so they cannot be cited and are not part of the chapter. */
  function headingBefore(start) {
    var root = article();
    var node = start;
    while (node && node !== root) {
      var sib = node.previousElementSibling;
      while (sib) {
        if (/^H[1-6]$/.test(sib.tagName) && HEADING_ID.test(sib.id)) return sib;
        var inner = sib.querySelectorAll(ANCHORED_HEADING);
        for (var i = inner.length - 1; i >= 0; i--) {
          if (HEADING_ID.test(inner[i].id)) return inner[i];
        }
        sib = sib.previousElementSibling;
      }
      node = node.parentElement;
    }
    return null;
  }

  function startsBefore(node, range) {
    var probe = document.createRange();
    try { probe.selectNode(node); } catch (_) { return false; }
    return probe.compareBoundaryPoints(Range.START_TO_START, range) <= 0;
  }

  function clip(text, size, fromEnd) {
    var flat = text.replace(/\s+/g, " ").trim();
    if (flat.length <= size) return flat;
    return fromEnd ? "…" + flat.slice(flat.length - size) : flat.slice(0, size) + "…";
  }

  function contextAround(range, block) {
    var out = { before: "", after: "" };
    if (!block) return out;
    try {
      var head = document.createRange();
      head.selectNodeContents(block);
      head.setEnd(range.startContainer, range.startOffset);
      out.before = clip(head.toString(), 200, true);
    } catch (_) {}
    try {
      var tail = document.createRange();
      tail.selectNodeContents(block);
      tail.setStart(range.endContainer, range.endOffset);
      out.after = clip(tail.toString(), 200, false);
    } catch (_) {}
    return out;
  }

  /* Inside a displayed Agda block, Agda's own highlighter has already named everything:
     each token carries its character offset as an id, and each definition additionally
     carries its Agda identifier. Walking the anchors up to the selection therefore
     recovers both the position to cite and the definition the reader is standing in. */
  function codeContext(range, block) {
    if (!block || block.tagName !== "PRE" || !block.classList.contains("Agda")) return null;
    var info = { token: "", definition: "" };
    var anchors = block.querySelectorAll("a[id]");
    for (var i = 0; i < anchors.length; i++) {
      if (!startsBefore(anchors[i], range)) break;
      var id = anchors[i].id;
      if (/^\d+$/.test(id)) info.token = id;
      else info.definition = id;
    }
    return info;
  }

  function linksInside(range) {
    var seen = [];
    var fragment;
    try { fragment = range.cloneContents(); } catch (_) { return seen; }
    var anchors = fragment.querySelectorAll("a[href]");
    for (var i = 0; i < anchors.length && seen.length < 10; i++) {
      var label = anchors[i].textContent.trim();
      var href = anchors[i].getAttribute("href");
      if (!label || !href || href.charAt(0) === "#") continue;
      /* Resolved against the address the handover quotes, not against the browser's
         own location, so a link copied out of a local preview still points somewhere
         an assistant can reach. */
      var full = href;
      try { full = new URL(href, pageUrl()).href; } catch (_) {}
      var pair = "`" + label + "`" + S.colon + full;
      if (seen.indexOf(pair) < 0) seen.push(pair);
    }
    return seen;
  }

  function describe(range) {
    var text = range.toString().replace(/\u00a0/g, " ").trim();
    if (!text) return null;
    var startBlock = blockOf(range.startContainer);
    var endBlock = blockOf(range.endContainer);
    var heading = headingBefore(startBlock || elementOf(range.startContainer));
    return {
      text: text,
      block: startBlock,
      endBlock: endBlock && endBlock !== startBlock ? endBlock : null,
      heading: heading,
      code: codeContext(range, startBlock),
      links: linksInside(range),
      context: contextAround(range, startBlock)
    };
  }

  /* ---- the handover document ---------------------------------------------- */

  function anchorOf(el) {
    return el && el.id ? "#" + el.id : "";
  }

  /* The deepest anchor the selection can be cited at: a numbered prose block, or, in a
     displayed Agda block, the character offset of the token the selection starts on. */
  function pointAnchor(info) {
    if (info.block && info.block.id) return "#" + info.block.id;
    if (info.code && info.code.token) return "#" + info.code.token;
    return "";
  }

  function handover(info) {
    var page = pageUrl();
    var origin = originUrl();
    var md = markdownUrl();
    var lines = [];
    function bullet(label, value) { if (value) lines.push("- " + label + S.colon + value); }
    function quoted(value) { return S.quoteOpen + value + S.quoteClose; }

    lines.push("# " + S.docTitle, "", S.intro, "", "## " + S.hSelection, "");
    /* A fence, so a selection that is itself Agda or Markdown cannot be mistaken for
       part of the instructions around it. */
    lines.push("```", info.text, "```", "", "## " + S.hWhere, "");
    bullet(S.fPage, page + pointAnchor(info));
    if (md) bullet(S.fMarkdown, md);
    if (!isLocal() && cfg.canonical && cfg.canonical !== page) {
      bullet(S.fCanonical, cfg.canonical);
    }
    if (cfg.external) {
      lines.push("- " + S.fLibrary);
      bullet(S.fModule, "`" + (cfg.chapter || "") + "`");
    } else {
      bullet(S.fChapter, quoted(cfg.title || "") + " (`" + (cfg.chapter || "") + "`)");
      if (cfg.order) {
        bullet(S.fReadingOrder, S.position(cfg.order, cfg.chapters || cfg.order));
      }
      bullet(S.fStage, cfg.stage);
    }
    /* `sec-0` is the chapter title, which the chapter line already gave. */
    if (info.heading && info.heading.id !== "sec-0") {
      bullet(S.fSection, quoted(info.heading.textContent.trim()) + " ("
             + page + anchorOf(info.heading) + ")");
    }
    if (info.block && info.block.id) bullet(S.fBlock, anchorOf(info.block));
    if (info.endBlock && info.endBlock.id) bullet(S.fSpans, anchorOf(info.endBlock));
    if (info.code) {
      lines.push("- " + S.fCode);
      if (info.code.definition) {
        bullet(S.fDefinition, "`" + info.code.definition + "` ("
               + page + "#" + info.code.definition + ")");
      }
      if (info.code.token) bullet(S.fToken, page + "#" + info.code.token);
    }
    if (info.context.before) bullet(S.fBefore, quoted(info.context.before));
    if (info.context.after) bullet(S.fAfter, quoted(info.context.after));
    if (info.links.length) {
      lines.push("- " + S.fLinks + S.colon.trim());
      info.links.forEach(function (pair) { lines.push("  - " + pair); });
    }
    if (cfg.agdaSource) bullet(S.fSource, cfg.agdaSource);
    if (cfg.prerequisites && cfg.prerequisites.length) {
      bullet(S.fPrereq, cfg.prerequisites.map(function (m) { return "`" + m + "`"; }).join(", "));
    }

    lines.push("", "## " + S.hProject, "");
    S.project.forEach(function (para) { lines.push(para, ""); });
    lines.push("## " + S.hFetch, "");
    S.fetch(origin, md ? S.mdNote(md) : S.mdRule).forEach(function (item) {
      if (item) lines.push("- " + item);
    });
    lines.push("", "## " + S.hWant, "");
    S.want.forEach(function (para) { lines.push(para, ""); });
    return lines.join("\n").replace(/\n{3,}/g, "\n\n").trim() + "\n";
  }

  /* ---- the trigger and the dialog ----------------------------------------- */

  var trigger = null;
  var dialog = null;
  var region = null;
  var status = null;
  var pending = "";
  var selecting = false;

  function buildTrigger() {
    trigger = document.createElement("button");
    trigger.type = "button";
    trigger.className = "ask-ai-trigger";
    trigger.hidden = true;
    trigger.title = S.triggerTitle;
    var glyph = document.createElement("span");
    glyph.className = "ask-ai-glyph";
    glyph.setAttribute("aria-hidden", "true");
    glyph.textContent = "✦";
    trigger.appendChild(glyph);
    trigger.appendChild(document.createTextNode(S.trigger));
    /* pointerdown would clear the selection before the click handler could read it. */
    trigger.addEventListener("mousedown", function (event) { event.preventDefault(); });
    trigger.addEventListener("click", function () { open(); });
    document.body.appendChild(trigger);
  }

  function buildDialog() {
    dialog = document.createElement("dialog");
    dialog.className = "ask-ai-dialog";
    dialog.setAttribute("aria-labelledby", "ask-ai-title");

    var head = document.createElement("div");
    head.className = "ask-ai-head";
    var title = document.createElement("h2");
    title.id = "ask-ai-title";
    title.textContent = S.dialogTitle;
    var dismiss = document.createElement("button");
    dismiss.type = "button";
    dismiss.className = "ask-ai-close";
    dismiss.setAttribute("aria-label", S.close);
    dismiss.textContent = "×";
    dismiss.addEventListener("click", close);
    head.appendChild(title);
    head.appendChild(dismiss);

    var hint = document.createElement("p");
    hint.className = "ask-ai-hint";
    hint.id = "ask-ai-hint";
    hint.textContent = S.hint;

    region = document.createElement("div");
    region.className = "ask-ai-copy";
    region.tabIndex = 0;
    region.setAttribute("role", "region");
    region.setAttribute("aria-label", S.regionLabel);
    region.setAttribute("aria-describedby", "ask-ai-hint");
    region.title = S.regionLabel;
    region.appendChild(document.createElement("pre"));
    /* A click copies, but a drag that selected part of the text must not: the reader
       who highlighted a fragment by hand meant to keep it highlighted. */
    region.addEventListener("click", function () {
      var picked = window.getSelection();
      if (picked && !picked.isCollapsed && region.contains(picked.anchorNode)) return;
      copy();
    });
    region.addEventListener("keydown", function (event) {
      if (event.key === "Enter" || event.key === " ") { event.preventDefault(); copy(); }
    });

    var foot = document.createElement("div");
    foot.className = "ask-ai-foot";
    status = document.createElement("p");
    status.className = "ask-ai-status";
    status.setAttribute("role", "status");
    status.setAttribute("aria-live", "polite");
    status.textContent = S.idle;
    var copyButton = document.createElement("button");
    copyButton.type = "button";
    copyButton.className = "ask-ai-button";
    copyButton.textContent = S.copy;
    copyButton.addEventListener("click", copy);
    var closeButton = document.createElement("button");
    closeButton.type = "button";
    closeButton.className = "ask-ai-button secondary";
    closeButton.textContent = S.close;
    closeButton.addEventListener("click", close);
    foot.appendChild(status);
    foot.appendChild(copyButton);
    foot.appendChild(closeButton);

    dialog.appendChild(head);
    dialog.appendChild(hint);
    dialog.appendChild(region);
    dialog.appendChild(foot);
    /* Clicking the backdrop lands on the dialog element itself, never on its children. */
    dialog.addEventListener("click", function (event) { if (event.target === dialog) close(); });
    document.body.appendChild(dialog);
  }

  function report(message, done) {
    status.textContent = message;
    if (done) status.dataset.done = "yes";
    else delete status.dataset.done;
  }

  function copy() {
    var text = pending;
    function fallback() {
      var box = document.createElement("textarea");
      box.value = text;
      box.setAttribute("readonly", "readonly");
      box.style.position = "fixed";
      box.style.top = "-1000px";
      document.body.appendChild(box);
      box.select();
      var ok = false;
      try { ok = document.execCommand("copy"); } catch (_) { ok = false; }
      document.body.removeChild(box);
      report(ok ? S.copied : S.failed, ok);
    }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function () { report(S.copied, true); }, fallback);
    } else {
      fallback();
    }
  }

  function hideTrigger() {
    if (trigger) trigger.hidden = true;
  }

  /* Viewport coordinates, recomputed from the live range on every scroll and resize.
     Document coordinates would be measured once and then drift, because KaTeX and the
     margin notes both reflow the article after the selection is made. */
  function placeTrigger(range) {
    var rects = range.getClientRects();
    var rect = rects.length ? rects[rects.length - 1] : range.getBoundingClientRect();
    if (!rect || (!rect.width && !rect.height)) return hideTrigger();
    if (rect.bottom < 0 || rect.top > window.innerHeight) return hideTrigger();
    trigger.hidden = false;
    var width = trigger.offsetWidth;
    var height = trigger.offsetHeight;
    var left = rect.right + 8;
    var top = rect.bottom - height;
    /* Beside the last line of the selection when there is room, otherwise tucked under
       it; never off an edge. */
    if (left + width > window.innerWidth - 10) {
      left = Math.max(10, Math.min(rect.left, window.innerWidth - width - 10));
      top = rect.bottom + 6;
    }
    top = Math.max(6, Math.min(top, window.innerHeight - height - 6));
    trigger.style.left = left + "px";
    trigger.style.top = top + "px";
  }

  function currentRange() {
    var picked = window.getSelection();
    if (!picked || picked.isCollapsed || !picked.rangeCount) return null;
    var range = picked.getRangeAt(0);
    var root = article();
    if (!root) return null;
    var start = elementOf(range.startContainer);
    var end = elementOf(range.endContainer);
    if (!start || !end || !root.contains(start) || !root.contains(end)) return null;
    if (dialog && (dialog.contains(start) || dialog.contains(end))) return null;
    if (range.toString().trim().length < 2) return null;
    return range;
  }

  function open() {
    var range = currentRange();
    if (!range) return;
    var info = describe(range);
    if (!info) return;
    pending = handover(info);
    region.firstChild.textContent = pending;
    report(S.idle, false);
    hideTrigger();
    if (dialog.showModal) dialog.showModal();
    else dialog.setAttribute("open", "open");
    region.focus();
  }

  function close() {
    if (dialog.close) dialog.close();
    else dialog.removeAttribute("open");
  }

  function refresh() {
    if (selecting) return hideTrigger();
    var range = currentRange();
    if (!range) return hideTrigger();
    placeTrigger(range);
  }

  document.addEventListener("DOMContentLoaded", function () {
    if (!article()) return;
    buildTrigger();
    buildDialog();
    var timer = null;
    function schedule() {
      if (timer) window.clearTimeout(timer);
      timer = window.setTimeout(refresh, 60);
    }
    document.addEventListener("selectionchange", function () {
      if (!selecting) schedule();
    });
    document.addEventListener("pointerup", function () {
      selecting = false;
      schedule();
    });
    document.addEventListener("pointercancel", function () {
      selecting = false;
      schedule();
    });
    document.addEventListener("keyup", function (event) {
      if (event.shiftKey || event.key === "Shift") schedule();
    });
    /* The trigger sits at the end of the body, so a keyboard reader who has just made a
       selection would have to tab a long way to reach it. Alt+A opens it in place. */
    document.addEventListener("keydown", function (event) {
      if (event.altKey && !event.ctrlKey && !event.metaKey
          && (event.key === "a" || event.key === "A" || event.code === "KeyA")) {
        if (currentRange()) { event.preventDefault(); open(); }
      }
    });
    document.addEventListener("pointerdown", function (event) {
      if (article().contains(event.target) && (!trigger || !trigger.contains(event.target))) {
        selecting = true;
        hideTrigger();
      }
      if (trigger && !trigger.contains(event.target)) hideTrigger();
    });
    window.addEventListener("scroll", function () {
      if (!trigger.hidden) refresh();
    }, { passive: true });
    window.addEventListener("resize", function () {
      if (!trigger.hidden) refresh();
    });
  });
})();
