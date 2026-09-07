(() => {
  "use strict";

  const host = document.getElementById("reading-explorer");
  if (!host) return;

  const lang = ["en", "zh", "ja"].includes(host.dataset.lang) ? host.dataset.lang : "en";
  const current = host.dataset.current || "Everything";
  const copy = {
    en: {
      title: "Choose a way through Bedrock",
      intro: "Routes share foundations and meet again at later chapters. Progress is saved only in this browser.",
      routeMode: "Topic routes", compareMode: "Compare", nextMode: "What next",
      progress: "complete", begin: "Start here", resume: "Continue", revisit: "Review route",
      viewRoute: "View route", inspectEntry: "View entry and prerequisites",
      compareIntro: "Select one to three routes. A chapter is ready when its direct prerequisites are complete.",
      select: "Select route", selected: "Selected route", shared: "Shared with",
      crossTopic: "Cross-topic prerequisites", outside: "prerequisites from other routes",
      done: "Completed", mark: "Mark complete", undo: "Mark incomplete", visit: "Open chapter",
      ready: "Ready", blocked: "Prerequisites to finish", preview: "Preview",
      nextIntro: "These chapters are ready from your completed prerequisites. Independent topics may be studied in either order.",
      noneReady: "Use the topic routes to review the prerequisites for your next chapter.",
      reset: "Reset progress", resetAsk: "Reset all reading progress saved in this browser?",
      compactDone: "Chapter complete", compactIntro: "Learning route",
      prerequisites: "Direct prerequisites", noPrerequisites: "No direct prerequisites",
      onward: "Possible next chapters", noOnward: "No direct continuation is listed yet.",
      allRoutes: "Explore all routes", loadError: "The interactive routes could not be loaded. The catalog and chapter links remain available.",
      recommended: "Recommended directory", depmap: "Dependency map",
      of: "of", routes: "Routes", needs: "Needs", module: "Module",
      allComplete: "All non-preview chapters are marked complete.", saved: "chapters complete"
    },
    ja: {
      title: "Bedrock の読書ルートを選ぶ",
      intro: "各ルートは基礎を共有し，後の章で合流します。進捗はこのブラウザだけに保存されます。",
      routeMode: "主題別ルート", compareMode: "並べて比較", nextMode: "次に読む章",
      progress: "完了", begin: "ここから読む", resume: "続きを読む", revisit: "ルートを復習",
      viewRoute: "ルートを見る", inspectEntry: "入口と前提を見る",
      compareIntro: "一つから三つのルートを選べます。直接の前提をすべて終えると，その章に進めます。",
      select: "ルートを選択", selected: "選択したルート", shared: "共有するルート",
      crossTopic: "他の主題の前提", outside: "件のルート外の前提",
      done: "完了", mark: "完了にする", undo: "未完了に戻す", visit: "章を開く",
      ready: "読めます", blocked: "先に読む前提", preview: "展望",
      nextIntro: "直接の前提を読み終えた章です。依存しない主題は，どちらからでも学べます。",
      noneReady: "主題別ルートで，次の章に必要な前提を確認できます。",
      reset: "進捗をリセット", resetAsk: "このブラウザに保存した読書の進捗をすべてリセットしますか？",
      compactDone: "この章は完了", compactIntro: "学習ルート",
      prerequisites: "直接の前提", noPrerequisites: "直接の前提はありません",
      onward: "次に進める章", noOnward: "直接続く章はありません。",
      allRoutes: "全ルートを見る", loadError: "ルートを読み込めませんでした。目次と章へのリンクは使えます。",
      recommended: "読書例の目次", depmap: "依存マップ",
      of: "/", routes: "ルート", needs: "必要", module: "モジュール",
      allComplete: "展望を除く全章を完了しました。", saved: "章を完了"
    },
    zh: {
      title: "探索 Bedrock 的阅读路线",
      intro: "各路线共享基础，并在后续章节汇合。进度仅保存在当前浏览器中。",
      routeMode: "主题路线", compareMode: "并排比较", nextMode: "下一步",
      progress: "已完成", begin: "从这里开始", resume: "继续", revisit: "回顾路线",
      viewRoute: "查看路线", inspectEntry: "查看入口与先修",
      compareIntro: "请选择一至三条路线。完成一章的全部直接先修后，该章即可阅读。",
      select: "选择路线", selected: "已选路线", shared: "同时属于",
      crossTopic: "跨主题先修", outside: "项路线外先修",
      done: "已完成", mark: "标记完成", undo: "取消完成", visit: "前往章节",
      ready: "可以开始", blocked: "尚待完成的先修", preview: "预览",
      nextIntro: "以下章节的直接先修均已完成。彼此没有依赖路径的主题可以任选次序。",
      noneReady: "可以返回主题路线，查看下一章所需的先修。",
      reset: "重置进度", resetAsk: "确定重置当前浏览器中保存的全部阅读进度吗？",
      compactDone: "本章已完成", compactIntro: "学习路线",
      prerequisites: "直接先修", noPrerequisites: "没有直接先修",
      onward: "可选后续章节", noOnward: "目前没有列出直接后续。",
      allRoutes: "查看全部路线", loadError: "交互路线暂时无法载入，原目录与章节链接仍可使用。",
      recommended: "推荐目录", depmap: "依赖地图",
      of: "/", routes: "路线", needs: "需补", module: "模块",
      allComplete: "所有非预览章节均已标记完成。", saved: "章已完成"
    }
  }[lang];

  const storageKey = "bedrock-reading-progress-v1";
  const el = (tag, cls, text) => {
    const node = document.createElement(tag);
    if (cls) node.className = cls;
    if (text !== undefined) node.textContent = text;
    return node;
  };
  const button = (text, cls, action) => {
    const node = el("button", cls, text);
    node.type = "button";
    node.addEventListener("click", action);
    return node;
  };
  const local = value => value && (value[lang] || value.en || value.zh) || "";
  const chapterHref = id => id === "Everything" ? "index.html" : `${encodeURIComponent(id)}.html`;

  let completed = new Set();
  try {
    const saved = JSON.parse(localStorage.getItem(storageKey) || "[]");
    if (Array.isArray(saved)) completed = new Set(saved.filter(x => typeof x === "string"));
  } catch (_) { /* A blocked or corrupt store simply starts empty. */ }

  const save = () => {
    try { localStorage.setItem(storageKey, JSON.stringify([...completed])); } catch (_) { /* optional */ }
  };

  fetch(host.dataset.source || "reading-routes.json", { credentials: "same-origin" })
    .then(response => {
      if (!response.ok) throw new Error(String(response.status));
      return response.json();
    })
    .then(data => {
      if (!data || data.version !== 1 || !Array.isArray(data.routes) || !Array.isArray(data.nodes)) {
        throw new Error("unsupported route data");
      }
      initialise(data);
    })
    .catch(() => {
      const note = el("p", "reading-load-error", copy.loadError);
      note.setAttribute("role", "status");
      host.append(note);
    });

  function initialise(data) {
    const nodes = new Map(data.nodes.map(node => [node.id, node]));
    const routes = new Map(data.routes.map(route => [route.id, route]));
    const validCompleted = [...completed].filter(id => nodes.has(id));
    completed = new Set(validCompleted);
    save();

    const prerequisites = node => (node.prerequisites || [])
      .map(id => nodes.get(id)).filter(node => node && !node.preview);
    const missing = node => prerequisites(node).filter(node => !completed.has(node.id));
    const ready = node => missing(node).length === 0;
    const routeNodes = route => (route.chapters || []).map(id => nodes.get(id)).filter(Boolean);
    const requiredRouteNodes = route => routeNodes(route).filter(node => !node.preview);
    const routeProgress = route => {
      const list = requiredRouteNodes(route);
      return { done: list.filter(node => completed.has(node.id)).length, total: list.length };
    };
    const firstEntry = route => routeNodes(route).find(node => !node.preview && !completed.has(node.id) && ready(node))
      || routeNodes(route).find(node => !node.preview && !completed.has(node.id))
      || requiredRouteNodes(route)[0];

    host.replaceChildren();
    host.classList.add("reading-explorer-ready");
    if (current !== "Everything") {
      renderCompact(nodes.get(current), nodes, routes, prerequisites, missing, ready);
      return;
    }

    let mode = "routes";
    let selected = data.routes.slice(0, Math.min(2, data.routes.length)).map(route => route.id);
    const viewKey = "bedrock-reading-view-v1";
    try {
      const savedView = JSON.parse(localStorage.getItem(viewKey) || "null");
      if (savedView && ["routes", "compare", "next"].includes(savedView.mode)) mode = savedView.mode;
      if (savedView && Array.isArray(savedView.selected)) {
        const known = [...new Set(savedView.selected)].filter(id => routes.has(id)).slice(0, 3);
        if (known.length) selected = known;
      }
    } catch (_) { /* View preferences are optional. */ }
    const shell = el("div", "reading-shell");
    const head = el("div", "reading-head");
    const heading = el("h2", "reading-title", copy.title);
    heading.id = "reading-explorer-title";
    head.append(heading, el("p", "reading-intro", copy.intro));
    shell.setAttribute("aria-labelledby", heading.id);

    const toolbar = el("div", "reading-toolbar");
    toolbar.setAttribute("role", "toolbar");
    toolbar.setAttribute("aria-label", copy.routes);
    const modes = [
      ["routes", copy.routeMode], ["compare", copy.compareMode], ["next", copy.nextMode]
    ];
    const modeButtons = new Map();
    for (const [id, label] of modes) {
      const control = button(label, "reading-mode", () => { mode = id; render(`mode:${id}`); });
      control.setAttribute("aria-pressed", "false");
      control.dataset.focus = `mode:${id}`;
      modeButtons.set(id, control);
      toolbar.append(control);
    }
    const reset = button(copy.reset, "reading-reset", () => {
      if (window.confirm(copy.resetAsk)) {
        completed.clear(); save(); render();
      }
    });
    toolbar.append(reset);
    const body = el("div", "reading-body");
    const live = el("p", "reading-live");
    live.setAttribute("aria-live", "polite");
    live.setAttribute("aria-atomic", "true");
    shell.append(head, toolbar, live, body);
    host.append(shell);

    function toggleDone(id) {
      completed.has(id) ? completed.delete(id) : completed.add(id);
      save();
      if (mode === "next" && completed.has(id)) {
        const next = data.nodes.find(node => !node.preview && !completed.has(node.id) && ready(node));
        render(next ? `done:${next.id}` : "mode:next");
      } else render(`done:${id}`);
    }

    function render(focusKey) {
      try { localStorage.setItem(viewKey, JSON.stringify({ mode, selected })); } catch (_) { /* optional */ }
      for (const [id, control] of modeButtons) {
        const active = id === mode;
        control.setAttribute("aria-pressed", String(active));
        control.classList.toggle("is-active", active);
      }
      body.replaceChildren();
      if (mode === "routes") renderRouteCards();
      else if (mode === "compare") renderComparison();
      else renderNext();
      const total = data.nodes.filter(node => !node.preview).length;
      const done = data.nodes.filter(node => !node.preview && completed.has(node.id)).length;
      live.textContent = `${done} ${copy.of} ${total} ${copy.saved}`;
      if (focusKey) requestAnimationFrame(() => {
        const target = [...shell.querySelectorAll("[data-focus]")]
          .find(node => node.dataset.focus === focusKey);
        if (target) target.focus({ preventScroll: true });
      });
    }

    function renderRouteCards() {
      const grid = el("div", "route-grid");
      for (const route of data.routes) {
        const progress = routeProgress(route);
        const card = el("article", "route-card");
        const top = el("div", "route-card-head");
        top.append(el("h3", "route-title", local(route.title)));
        const count = el("span", "route-count", `${progress.done} ${copy.of} ${progress.total} ${copy.progress}`);
        top.append(count);
        const meter = el("div", "route-meter");
        meter.setAttribute("role", "progressbar");
        meter.setAttribute("aria-valuemin", "0");
        meter.setAttribute("aria-valuemax", String(progress.total));
        meter.setAttribute("aria-valuenow", String(progress.done));
        meter.setAttribute("aria-label", local(route.title));
        const fill = el("span", "route-meter-fill");
        fill.style.width = `${progress.total ? progress.done / progress.total * 100 : 0}%`;
        meter.append(fill);
        card.append(top, el("p", "route-description", local(route.description)), meter);
        const routeIds = new Set((route.chapters || []));
        const outside = [];
        const seen = new Set();
        for (const node of routeNodes(route)) {
          for (const gap of missing(node)) {
            if (!routeIds.has(gap.id) && !seen.has(gap.id)) {
              seen.add(gap.id); outside.push(gap);
            }
          }
        }
        if (outside.length) card.append(prerequisiteDetails(outside, `${copy.needs} ${outside.length} ${copy.outside}`));
        const entry = firstEntry(route);
        if (entry) {
          const entryReady = ready(entry);
          const label = !entryReady ? copy.inspectEntry : progress.done === 0 ? copy.begin : progress.done < progress.total ? copy.resume : copy.revisit;
          const link = el("a", "route-entry", label);
          link.href = chapterHref(entry.id);
          link.append(el("span", "route-entry-name", local(entry.title)));
          card.append(link);
        }
        const view = button(copy.viewRoute, "route-view", () => {
          selected = [route.id]; mode = "compare"; render(`route:${route.id}`);
        });
        view.dataset.focus = `view:${route.id}`;
        card.append(view);
        grid.append(card);
      }
      body.append(grid);
    }

    function renderComparison() {
      body.append(el("p", "reading-view-intro", copy.compareIntro));
      const picker = el("div", "route-picker");
      for (const route of data.routes) {
        const active = selected.includes(route.id);
        const control = button(local(route.title), "route-pick", () => {
          if (selected.includes(route.id)) {
            if (selected.length > 1) selected = selected.filter(id => id !== route.id);
          } else if (selected.length < 3) selected = [...selected, route.id];
          render(`route:${route.id}`);
        });
        control.setAttribute("aria-pressed", String(active));
        control.setAttribute("aria-label", `${active ? copy.selected : copy.select}: ${local(route.title)}`);
        control.classList.toggle("is-active", active);
        control.disabled = !active && selected.length >= 3;
        control.dataset.focus = `route:${route.id}`;
        picker.append(control);
      }
      body.append(picker);
      const columns = el("div", "route-columns");
      columns.style.setProperty("--route-columns", String(selected.length));
      for (const routeId of selected) {
        const route = routes.get(routeId);
        if (!route) continue;
        const column = el("section", "route-column");
        column.append(el("h3", "route-column-title", local(route.title)));
        for (const node of routeNodes(route)) column.append(chapterCard(node, routeId));
        columns.append(column);
      }
      body.append(columns);
    }

    function chapterCard(node, routeId) {
      const isDone = completed.has(node.id);
      const gaps = missing(node);
      const card = el("article", `chapter-card${isDone ? " is-done" : gaps.length ? " is-blocked" : " is-ready"}`);
      card.dataset.chapter = node.id;
      const meta = el("div", "chapter-meta");
      meta.append(el("span", "chapter-stage", local(node.stage)));
      const state = el("span", "chapter-state", node.preview ? copy.preview : isDone ? copy.done : gaps.length ? copy.blocked : copy.ready);
      meta.append(state);
      const title = el("a", "chapter-title", local(node.title));
      title.href = chapterHref(node.id);
      card.append(meta, title, el("div", "chapter-module", node.id));
      const peers = (node.routes || []).filter(id => id !== routeId && routes.has(id));
      if (peers.length) card.append(el("p", "chapter-shared", `${copy.shared}: ${peers.map(id => local(routes.get(id).title)).join(" · ")}`));
      const ownRoutes = new Set(node.routes || []);
      const prerequisiteRoutes = new Set();
      for (const prerequisite of prerequisites(node)) {
        for (const id of prerequisite.routes || []) if (!ownRoutes.has(id)) prerequisiteRoutes.add(id);
      }
      if (prerequisiteRoutes.size || prerequisites(node).filter(item => (item.routes || []).length > 1).length > 1) {
        card.append(el("p", "chapter-cross", copy.crossTopic));
      }
      if (gaps.length) card.append(prerequisiteDetails(gaps, `${copy.needs} ${gaps.length}: ${copy.blocked}`));
      if (!node.preview) {
        const actions = el("div", "chapter-actions");
        const doneControl = button(isDone ? copy.undo : copy.mark, "chapter-done", () => toggleDone(node.id));
        doneControl.setAttribute("aria-pressed", String(isDone));
        doneControl.dataset.focus = `done:${node.id}`;
        actions.append(doneControl);
        const visit = el("a", "chapter-open", copy.visit);
        visit.href = chapterHref(node.id);
        actions.append(visit);
        card.append(actions);
      }
      return card;
    }

    function prerequisiteDetails(items, label) {
      const details = el("details", "chapter-prerequisites");
      details.append(el("summary", "", label));
      const list = el("ul", "");
      for (const item of items) {
        const row = el("li", "");
        const link = el("a", "", local(item.title));
        link.href = chapterHref(item.id);
        row.append(link);
        list.append(row);
      }
      details.append(list);
      return details;
    }

    function renderNext() {
      body.append(el("p", "reading-view-intro", copy.nextIntro));
      const candidates = data.nodes.filter(node => !node.preview && !completed.has(node.id) && ready(node));
      const grid = el("div", "next-grid");
      for (const node of candidates) grid.append(chapterCard(node, ""));
      if (!candidates.length) {
        const allDone = data.nodes.filter(node => !node.preview).every(node => completed.has(node.id));
        body.append(el("p", "reading-empty", allDone ? copy.allComplete : copy.noneReady));
      }
      else body.append(grid);
    }

    render();
  }

  function renderCompact(node, nodes, routes, prerequisites, missing, ready) {
    if (!node) return;
    const wasOpen = host.querySelector(".reading-compact")?.open || false;
    const wrap = el("details", "reading-compact");
    wrap.open = wasOpen;
    const summary = el("summary", "compact-summary", copy.compactIntro);
    const top = el("div", "compact-top");

    const doneControl = button(completed.has(node.id) ? copy.compactDone : copy.mark, "compact-done", () => {
      completed.has(node.id) ? completed.delete(node.id) : completed.add(node.id);
      save(); renderCompact(node, nodes, routes, prerequisites, missing, ready);
      requestAnimationFrame(() => host.querySelector(".compact-done")?.focus({ preventScroll: true }));
    });
    doneControl.setAttribute("aria-pressed", String(completed.has(node.id)));
    if (!node.preview) top.append(doneControl);
    const details = el("div", "compact-details");
    const prereq = prerequisites(node);
    details.append(compactList(copy.prerequisites, prereq, item => completed.has(item.id)));
    const successors = [...nodes.values()].filter(item => (item.prerequisites || []).includes(node.id)).slice(0, 5);
    details.append(compactList(copy.onward, successors, item => ready(item)));
    const all = el("a", "compact-all", copy.allRoutes);
    all.href = "index.html#reading-explorer";
    wrap.append(summary, top, details, all, el("p", "compact-storage", copy.intro));
    host.replaceChildren(wrap);
  }

  function compactList(label, items, positive) {
    const group = el("div", "compact-group");
    group.append(el("h3", "compact-label", label));
    if (!items.length) {
      group.append(el("p", "compact-empty", label === copy.prerequisites ? copy.noPrerequisites : copy.noOnward));
      return group;
    }
    const list = el("ul", "compact-list");
    for (const item of items) {
      const li = el("li", positive(item) ? "is-positive" : "is-pending");
      const link = el("a", "", local(item.title));
      link.href = chapterHref(item.id);
      li.append(link);
      list.append(li);
    }
    group.append(list);
    return group;
  }
})();
