/* Bedrock reader: current-route. AGPL-3.0-only. */
import { cfg } from "./document.js";
import { routes, preferredRoute, routeChanged } from "./route-store.js";

  /* Prefer the selected route when it contains the current chapter. */
  function initCurrentRoute() {
    var section = document.querySelector("#toc .current-route");
    if (!section) return;
    var list = section.querySelector(".route-nav");
    var name = section.querySelector(".current-route-name");
    var current = section.dataset.current;
    var data = null;
    function showRoute() {
      if (!data) return;
      var preferred = preferredRoute();
      var route = data.routes.find(function (item) {
        return item.id === preferred && (!current || item.chapters.includes(current));
      }) || data.routes.find(function (item) { return item.chapters.includes(current); })
        || data.routes[0];
      if (!route) return;
      var nodes = new Map(data.nodes.map(function (node) { return [node.id, node]; }));
      name.textContent = route.title[cfg.lang] || route.title.en;
      list.dataset.route = route.id;
      list.replaceChildren();
      route.chapters.forEach(function (id) {
        var node = nodes.get(id);
        if (!node) return;
        var item = document.createElement("li");
        var link = document.createElement("a");
        link.href = node.page + node.anchor;
        link.dataset.chapter = id;
        link.textContent = node.title[cfg.lang] || node.title.en;
        if (id === current) link.setAttribute("aria-current", "page");
        item.appendChild(link);
        list.appendChild(item);
      });
    }
    window.addEventListener(routeChanged, showRoute);
    routes()
      .then(function (loaded) { data = loaded; showRoute(); })
      .catch(function () { /* The server-rendered route remains usable. */ });
  }

export { initCurrentRoute };
