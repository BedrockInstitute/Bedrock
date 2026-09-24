/* Bedrock appearance: one semantic palette for every Agda rendering surface.
 * Classic themes are contrast-adjusted adaptations, not editor token grammars.
 * Sources and mapping: site/README.md. No network request or dependency. */
(function () {
  "use strict";
  var root = document.documentElement;
  var fields = ["bg", "fg", "border", "comment", "keyword", "symbol", "string",
    "number", "module", "field", "macro", "constructor", "identifier"];
  var palettes = {
    github: {
      light: ["#f6f8fa", "#24292f", "#d0d7de", "#57606a", "#cf222e", "#825f23", "#953800", "#0550ae", "#8250df", "#a42c83", "#6639ba", "#116329", "#0550ae"],
      dark: ["#0d1117", "#e6edf3", "#30363d", "#8b949e", "#ff7b72", "#e3b86d", "#a5d6ff", "#79c0ff", "#d2a8ff", "#ff9bce", "#d2a8ff", "#7ee787", "#79c0ff"]
    },
    solarized: {
      light: ["#fdf6e3", "#586e75", "#d9d2be", "#5e727a", "#b34414", "#876600", "#a52c68", "#635cab", "#a52c68", "#635cab", "#996012", "#596b00", "#176fa6"],
      dark: ["#002b36", "#a7b5b5", "#27505a", "#93a1a1", "#f08c55", "#d5b351", "#ed86b1", "#aaa6ec", "#ed86b1", "#aaa6ec", "#d5b351", "#adbd52", "#69b9ee"]
    },
    catppuccin: {
      light: ["#eff1f5", "#4c4f69", "#ccd0da", "#626880", "#b84d19", "#85612b", "#b52646", "#8839ef", "#a52d86", "#8839ef", "#9e550b", "#347519", "#1b60e5"],
      dark: ["#1e1e2e", "#cdd6f4", "#45475a", "#a6adc8", "#fab387", "#f9e2af", "#f38ba8", "#cba6f7", "#f5c2e7", "#cba6f7", "#f9e2af", "#a6e3a1", "#89b4fa"]
    },
    gruvbox: {
      light: ["#fbf1c7", "#3c3836", "#d5c4a1", "#716453", "#af3a03", "#876517", "#9d0006", "#8f3f71", "#8f3f71", "#8f3f71", "#945613", "#626900", "#076678"],
      dark: ["#282828", "#ebdbb2", "#504945", "#bdae93", "#fe8019", "#e7c477", "#fb9390", "#d3869b", "#d3869b", "#d3869b", "#fabd2f", "#b8bb26", "#83a598"]
    }
  };
  var keys = fields.map(function (name) { return "--code-" + name; }).concat(
    ["--code-inline-bg", "--code-popup-bg", "--occ-bg"]);
  function validPalette(value) {
    return typeof value === "string" && Object.prototype.hasOwnProperty.call(palettes, value) ? value : "default";
  }
  function read(key) { try { return localStorage.getItem(key); } catch (_) { return null; } }
  function write(key, value) { try { localStorage.setItem(key, value); } catch (_) {} }
  function validMode(value) { return value === "light" || value === "dark" ? value : "system"; }
  function readPalettes() {
    var value;
    try { value = JSON.parse(read("bedrock-code-palettes")); } catch (_) {}
    return {light: validPalette(value && value.light), dark: validPalette(value && value.dark)};
  }
  var preferences = readPalettes(), mode = validMode(read("bedrock-theme"));
  var inheritedMode = null;
  var system = window.matchMedia("(prefers-color-scheme: dark)");
  var panel, trigger;
  function effectiveMode() { return inheritedMode || (mode === "system" ? (system.matches ? "dark" : "light") : mode); }
  function paint(element, name, scheme) {
    keys.forEach(function (key) { element.style.removeProperty(key); });
    if (name === "default") return;
    var colors = palettes[name][scheme];
    fields.forEach(function (field, index) { element.style.setProperty("--code-" + field, colors[index]); });
    element.style.setProperty("--code-inline-bg", colors[0]);
    element.style.setProperty("--code-popup-bg", colors[0]);
    element.style.setProperty("--occ-bg", scheme === "dark" ? "#d5bd5929" : "#bd8b0014");
  }
  function syncFrame(frame) {
    try {
      if (frame.contentWindow.bedrockAppearance) {
        frame.contentWindow.bedrockAppearance.inherit(effectiveMode(), preferences);
        frame.style.colorScheme = effectiveMode();
      }
    } catch (_) { /* An external frame is not part of the definition mirror. */ }
  }
  function apply() {
    var scheme = effectiveMode();
    root.classList.toggle("theme-light", scheme === "light");
    root.classList.toggle("theme-dark", scheme === "dark");
    root.dataset.appearanceMode = scheme;
    root.dataset.codePalette = preferences[scheme];
    root.style.colorScheme = scheme;
    paint(root, preferences[scheme], scheme);
    if (panel) {
      panel.querySelectorAll("[data-appearance-mode]").forEach(function (button) {
        button.setAttribute("aria-pressed", String(button.dataset.appearanceMode === mode));
      });
      ["light", "dark"].forEach(function (theme) {
        panel.querySelector("#code-palette-" + theme).value = preferences[theme];
        paint(panel.querySelector("[data-preview='" + theme + "']"), preferences[theme], theme);
      });
    }
    document.querySelectorAll("iframe.definition-modal-frame").forEach(syncFrame);
  }
  function setMode(value) {
    mode = validMode(value); inheritedMode = null;
    write("bedrock-theme", mode); apply();
  }
  function setPalette(scheme, value) {
    if (scheme !== "light" && scheme !== "dark") return;
    preferences[scheme] = validPalette(value);
    write("bedrock-code-palettes", JSON.stringify(preferences)); apply();
  }
  window.bedrockAppearance = {
    apply: apply, setMode: setMode, setPalette: setPalette, syncFrame: syncFrame,
    effectiveMode: effectiveMode,
    inherit: function (scheme, values) {
      inheritedMode = validMode(scheme);
      preferences = {light: validPalette(values.light), dark: validPalette(values.dark)};
      apply();
    }
  };
  apply(); // Synchronous head script: palette is applied before the first paint.
  system.addEventListener("change", apply);
  window.addEventListener("storage", function (event) {
    if (event.key === null || event.key === "bedrock-code-palettes" || event.key === "bedrock-theme") {
      preferences = readPalettes(); mode = validMode(read("bedrock-theme"));
      if (window.parent !== window) {
        try { inheritedMode = window.parent.bedrockAppearance.effectiveMode(); } catch (_) {}
      }
      apply();
    }
  });
  document.addEventListener("DOMContentLoaded", function () {
    trigger = document.getElementById("theme-toggle");
    if (!trigger) return;
    var messages = {
      en: ["Appearance", "Page theme", "System", "Light", "Dark", "Agda highlighting", "Default", "Light palette", "Dark palette", "Saved separately for each mode. Changes apply throughout the book.", "Close appearance settings"],
      zh: ["外观设置", "页面模式", "跟随系统", "浅色", "深色", "Agda 代码配色", "默认", "浅色配色", "深色配色", "深浅模式分别记忆，应用于全书所有代码与提示窗口。", "关闭外观设置"],
      ja: ["外観設定", "ページの表示", "システム", "ライト", "ダーク", "Agda の配色", "デフォルト", "ライトの配色", "ダークの配色", "モード別に保存し、本文とすべてのコード・ヒントに適用します。", "外観設定を閉じる"]
    };
    var t = messages[document.documentElement.lang] || messages.en;
    trigger.title = t[0]; trigger.setAttribute("aria-label", t[0]);
    trigger.setAttribute("aria-expanded", "false"); trigger.setAttribute("aria-controls", "appearance-panel");
    trigger.setAttribute("aria-haspopup", "dialog");
    trigger.innerHTML = '<svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="8"/><path d="M12 4a8 8 0 0 1 0 16Z" fill="currentColor" stroke="none"/></svg>';
    panel = document.createElement("section"); panel.id = "appearance-panel"; panel.hidden = true;
    panel.setAttribute("role", "dialog"); panel.setAttribute("aria-labelledby", "appearance-title");
    var heading = document.createElement("div"); heading.className = "appearance-heading";
    var title = document.createElement("h2"); title.id = "appearance-title"; title.textContent = t[0]; heading.appendChild(title);
    var close = document.createElement("button"); close.type = "button"; close.className = "appearance-close";
    close.textContent = "×"; close.setAttribute("aria-label", t[10]); heading.appendChild(close); panel.appendChild(heading);
    var modes = document.createElement("fieldset"); var legend = document.createElement("legend"); legend.textContent = t[1]; modes.appendChild(legend);
    var group = document.createElement("div"); group.className = "appearance-modes";
    ["system", "light", "dark"].forEach(function (theme, index) {
      var button = document.createElement("button"); button.type = "button";
      button.dataset.appearanceMode = theme; button.textContent = t[index + 2];
      button.addEventListener("click", function () { setMode(theme); }); group.appendChild(button);
    });
    modes.appendChild(group); panel.appendChild(modes);
    var code = document.createElement("fieldset"); legend = document.createElement("legend"); legend.textContent = t[5]; code.appendChild(legend);
    ["light", "dark"].forEach(function (theme, index) {
      var row = document.createElement("div"); row.className = "appearance-palette";
      var label = document.createElement("label"); label.htmlFor = "code-palette-" + theme; label.textContent = t[index + 7]; row.appendChild(label);
      var select = document.createElement("select"); select.id = label.htmlFor;
      ["default", "github", "solarized", "catppuccin", "gruvbox"].forEach(function (name, i) {
        var option = document.createElement("option"); option.value = name;
        option.textContent = [t[6], "GitHub", "Solarized", "Catppuccin · " + (theme === "light" ? "Latte" : "Mocha"), "Gruvbox"][i]; select.appendChild(option);
      });
      select.addEventListener("change", function () { setPalette(theme, select.value); }); row.appendChild(select);
      var preview = document.createElement("div"); preview.className = "appearance-preview Agda theme-" + theme;
      preview.dataset.preview = theme; preview.setAttribute("aria-hidden", "true");
      preview.innerHTML = '<span class="Keyword">data</span> <span class="Datatype">Bool</span> <span class="Symbol syntax-symbol">:</span> <span class="Primitive">Type</span> <span class="Keyword">where</span><br>  <span class="InductiveConstructor">true false</span> <span class="Symbol syntax-symbol">:</span> <span class="Datatype">Bool</span>';
      row.appendChild(preview); code.appendChild(row);
    });
    panel.appendChild(code);
    var help = document.createElement("p"); help.className = "appearance-help"; help.textContent = t[9]; panel.appendChild(help);
    document.getElementById("site-header").appendChild(panel);
    function hide(focus) { panel.hidden = true; trigger.setAttribute("aria-expanded", "false"); if (focus) trigger.focus(); }
    trigger.addEventListener("click", function () {
      var opening = panel.hidden; panel.hidden = !opening; trigger.setAttribute("aria-expanded", String(opening));
      if (opening) close.focus();
    });
    close.addEventListener("click", function () { hide(true); });
    document.addEventListener("pointerdown", function (event) {
      if (!panel.hidden && !panel.contains(event.target) && !trigger.contains(event.target)) hide(false);
    });
    document.addEventListener("keydown", function (event) {
      if (!panel.hidden && event.key === "Escape") { event.preventDefault(); hide(true); }
    });
    document.addEventListener("focusin", function (event) {
      if (!panel.hidden && !panel.contains(event.target) && !trigger.contains(event.target)) hide(false);
    });
    apply();
  });
})();
