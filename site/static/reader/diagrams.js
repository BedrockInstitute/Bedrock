/* Bedrock reader: diagrams. AGPL-3.0-only. */

(function () {
  "use strict";
  document.addEventListener("DOMContentLoaded", function () {
    const figure = document.getElementById("fig-fiber-general");
    if (!figure) return;
    const trigger = figure.querySelector(".fiber-fan-stage");
    const bundles = Array.from(figure.querySelectorAll(".fiber-bundle"));
    if (!trigger || !bundles.length) return;
    const numbers = /-?\d+(?:\.\d+)?/g;
    const coordinates = data => data.match(numbers).map(Number);
    const position = node => [Number(node.getAttribute("cx")), Number(node.getAttribute("cy"))];
    const morphs = [], points = [], labels = [];
    const centreLabels = Array.from(figure.querySelectorAll(".fiber-center-label"));
    bundles.forEach(bundle => {
      const target = coordinates(bundle.dataset.centerPath);
      const [ax, iy] = target.slice(-2);
      const ay = position(bundle.querySelector(".fiber-domain-point"))[1];
      // Merge whole paths into p_i; the fixed base and the image remain distinct.
      const targets = [
        [".fiber-hair", target],
        [".fiber-moving-map", [ax, ay + 4, ax, iy - 10]],
        [".fiber-moving-tip", [ax - 4, iy - 17, ax, iy - 10, ax + 4, iy - 17]]
      ];
      targets.forEach(([selector, to]) => {
        bundle.querySelectorAll(selector).forEach(node => {
          morphs.push({node, to, from: coordinates(node.getAttribute("d")), template: node.getAttribute("d")});
        });
      });
      [[".fiber-domain-point", [ax, ay]], [".fiber-image-point", [ax, iy]]].forEach(([selector, to]) => {
        bundle.querySelectorAll(selector).forEach(node => points.push({node, to, from: position(node)}));
      });
      const width = bundle.ownerSVGElement.viewBox.baseVal.width;
      figure.querySelectorAll(`.fiber-sample-label[data-fiber="${bundle.dataset.fiber}"]`).forEach(node => {
        labels.push({node, from: parseFloat(node.style.left), to: ax / width * 100});
      });
    });
    const text = ({
      en: ["Contract the three fibres to their centres", "Expand the three fibres again"],
      zh: ["将三束纤维收向各自的中心", "重新展开三束纤维"],
      ja: ["三つのファイバーをそれぞれの中心へ収縮する", "三つのファイバーを再び広げる"]
    })[document.documentElement.lang] || ["Contract the three fibres to their centres", "Expand the three fibres again"];
    let contracted = false;
    function paint(t) {
      morphs.forEach(({node, from, to, template}) => {
        let i = 0;
        node.setAttribute("d", template.replace(numbers, () => {
          const n = i++;
          return String(from[n] + (to[n] - from[n]) * t);
        }));
      });
      points.forEach(({node, from, to}) => {
        node.setAttribute("cx", from[0] + (to[0] - from[0]) * t);
        node.setAttribute("cy", from[1] + (to[1] - from[1]) * t);
      });
      labels.forEach(({node, from, to}) => {
        node.style.left = (from + (to - from) * t) + "%";
        node.style.opacity = String(Math.max(0, 1 - t / .55));
        node.setAttribute("aria-hidden", String(t >= .55));
      });
      centreLabels.forEach(node => {
        node.style.opacity = t === 1 ? "1" : "0";
        node.setAttribute("aria-hidden", String(t !== 1));
      });
    }
    trigger.setAttribute("role", "button");
    trigger.setAttribute("aria-label", text[0]);
    trigger.setAttribute("aria-pressed", "false");
    trigger.tabIndex = 0;
    figure.classList.add("fiber-interactive");
    trigger.addEventListener("keydown", event => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        trigger.click();
      }
    });
    trigger.addEventListener("click", () => {
      if (figure.classList.contains("fiber-animating")) return;
      figure.classList.add("fiber-animating");
      trigger.setAttribute("aria-disabled", "true");
      let start;
      function frame(now) {
        if (start === undefined) start = now;
        const time = Math.min(1, (now - start) / 3600);
        const eased = time * time * (3 - 2 * time);
        paint(contracted ? 1 - eased : eased);
        if (time < 1) requestAnimationFrame(frame);
        else {
          contracted = !contracted;
          figure.classList.toggle("fiber-contracted", contracted);
          figure.classList.remove("fiber-animating");
          trigger.removeAttribute("aria-disabled");
          trigger.setAttribute("aria-pressed", String(contracted));
          trigger.setAttribute("aria-label", text[contracted ? 1 : 0]);
        }
      }
      requestAnimationFrame(frame);
    });
  });
})();

/* Expand the schematic family of paths into its type; paths become its points. */
(function () {
  "use strict";
  document.addEventListener("DOMContentLoaded", function () {
    const figure = document.getElementById("fig-coded-truth");
    if (!figure) return;
    const trigger = figure.querySelector(".coded-truth-trigger");
    const moving = figure.querySelector(".coded-truth-moving-space");
    const region = figure.querySelector(".coded-truth-region-copy");
    const targetSpace = figure.querySelector(".coded-truth-proof-target");
    if (!trigger || !moving || !region || !targetSpace) return;
    const targets = ["q", "r"].map(name => ({
      point: figure.querySelector(`.coded-truth-target-${name}`),
      copy: figure.querySelector(`.coded-truth-path-copy-${name}`)
    }));
    if (targets.some(target => !target.point || !target.copy)) return;
    const targetMarks = [...figure.querySelectorAll(".coded-truth-target")];
    const initialPath = region.getAttribute("d");
    const clamp = x => Math.max(0, Math.min(1, x));
    const smooth = x => { x = clamp(x); return x * x * (3 - 2 * x); };
    const arc = (t, control) => [100 + 210 * t, 95 + 2 * t * (1 - t) * (control - 95)];
    const source = Array.from({length: 64}, (_, i) =>
      i <= 32 ? arc(i / 32, 0) : arc((64 - i) / 32, 190));
    const labels = {
      en: "Unfold the highlighted path space",
      zh: "展开高亮的路径空间",
      ja: "強調されたパス空間を展開する"
    };
    trigger.setAttribute("role", "button");
    trigger.setAttribute("aria-label", labels[document.documentElement.lang] || labels.en);
    trigger.tabIndex = 0;
    figure.classList.add("coded-truth-interactive");
    trigger.addEventListener("keydown", function (event) {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        trigger.click();
      }
    });
    trigger.addEventListener("click", async function () {
      if (figure.classList.contains("coded-truth-playing")) return;
      trigger.setAttribute("aria-disabled", "true");
      figure.classList.add("coded-truth-playing");
      try {
        const matrix = moving.ownerSVGElement.getScreenCTM();
        if (!matrix) return;
        const inverse = matrix.inverse();
        const local = (x, y) => new DOMPoint(x, y).matrixTransform(inverse);
        const bounds = targetSpace.getBoundingClientRect();
        const topLeft = local(bounds.left, bounds.top);
        const bottomRight = local(bounds.right, bounds.bottom);
        const x = topLeft.x, y = topLeft.y, right = bottomRight.x, bottom = bottomRight.y;
        const middleY = (y + bottom) / 2;
        const radius = Math.min(8 / Math.hypot(matrix.a, matrix.b), (right - x) / 4, (bottom - y) / 4);
        const rectangle = `M${x} ${middleY} L${x} ${y + radius} Q${x} ${y} ${x + radius} ${y} ` +
          `L${right - radius} ${y} Q${right} ${y} ${right} ${y + radius} ` +
          `L${right} ${bottom - radius} Q${right} ${bottom} ${right - radius} ${bottom} ` +
          `L${x + radius} ${bottom} Q${x} ${bottom} ${x} ${bottom - radius} Z`;
        region.setAttribute("d", rectangle);
        const perimeter = region.getTotalLength();
        const destination = source.map((_, i) => region.getPointAtLength(perimeter * i / source.length));
        region.setAttribute("d", initialPath);
        const points = targets.map(target => {
          const box = target.point.getBoundingClientRect();
          return local(box.x + box.width / 2, box.y + box.height / 2);
        });
        await new Promise(resolve => {
          let started;
          function frame(now) {
            if (started === undefined) started = now;
            const time = clamp((now - started) / 4200);
            const progress = smooth((time - .1) / .72);
            const fade = 1 - smooth((time - .84) / .16);
            moving.style.opacity = String(smooth(time / .1));
            region.style.opacity = String(fade);
            region.setAttribute("d", source.map((point, i) =>
              `${i ? "L" : "M"}${point[0] + (destination[i].x - point[0]) * progress} ` +
              `${point[1] + (destination[i].y - point[1]) * progress}`).join(" ") + " Z");
            targets.forEach((target, i) => {
              const cx = 205 + (points[i].x - 205) * progress;
              const cy = 95 + (points[i].y - 95) * progress;
              target.copy.setAttribute("transform", `translate(${cx} ${cy}) scale(${1 - .98 * progress}) translate(-205 -95)`);
              target.copy.style.opacity = String(fade);
            });
            targetMarks.forEach(mark => { mark.style.opacity = String(1 - fade); });
            if (time < 1) requestAnimationFrame(frame);
            else resolve();
          }
          requestAnimationFrame(frame);
        });
      } finally {
        moving.style.opacity = "";
        region.style.opacity = "";
        region.setAttribute("d", initialPath);
        targets.forEach(target => {
          target.copy.removeAttribute("transform");
          target.copy.style.opacity = "";
        });
        targetMarks.forEach(mark => { mark.style.opacity = ""; });
        figure.classList.remove("coded-truth-playing");
        trigger.removeAttribute("aria-disabled");
      }
    });
  });
})();
