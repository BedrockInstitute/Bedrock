/* Compiler sidecars are shared by source ranges, names, syntax and popup code.
 * Only the renderer supplies semantics. This service never guesses a type. */
export function createTypeStore({ baseUrl = '', lang = 'en', fetcher = fetch }) {
  const requests = new Map();
  function get(module) {
    if (!requests.has(module)) {
      requests.set(module, fetcher(baseUrl + '/' + lang + '/types/' + module + '.json')
        .then(response => response.ok ? response.json() : Promise.reject(response.status))
        .catch(() => { requests.delete(module); return {}; }));
    }
    return requests.get(module);
  }
  async function resolve(target) {
    const expression = target.getAttribute('data-expression-type');
    const templateId = target.getAttribute('data-hover-template');
    const template = templateId && target.ownerDocument.getElementById(templateId);
    const infoHTML = target.getAttribute('data-hover-html') || (template && template.innerHTML);
    const helpKey = target.getAttribute('data-hover-help');
    const raw = expression || target.getAttribute('data-type');
    const spec = raw && raw.split('#');
    const types = helpKey ? await get('$syntax') : spec ? await get(spec[0]) : {};
    const node = expression && spec && types.$expressions && types.$expressions[spec[1]];
    return {
      html: infoHTML || (helpKey && types[helpKey]) ||
        (expression ? node && node.type : spec && types[spec[1]]),
      infoHTML, helpKey, template,
      name: spec && (types.$names || {})[spec[1]],
      hasDefinition: target.hasAttribute('href') && !infoHTML && !helpKey,
      hasChapterModal: target.hasAttribute('href') && target.getAttribute('data-hover-navigate') === 'modal'
    };
  }
  return Object.freeze({ get, resolve });
}
