/* A document's route data and current-route preference have one owner. */
import { cfg } from './document.js';
import { readPreference, writePreference } from './preferences.js';
const requests = new Map();
export const routeChanged = 'textbook:current-route';
export const preferredRoute = () => readPreference('current-route-v1') || '';
export function chooseRoute(id) {
  writePreference('current-route-v1', id);
  window.dispatchEvent(new Event(routeChanged));
}
export function routes(source = `${cfg.baseUrl || ''}/${cfg.lang || 'en'}/reading-routes.json`) {
  const url = new URL(source, document.baseURI).href;
  if (!requests.has(url)) {
    const pending = fetch(url, {credentials: 'same-origin'}).then(response => {
      if (!response.ok) throw new Error(String(response.status));
      return response.json();
    }).then(data => {
      if (!data || data.version !== 1 || !Array.isArray(data.routes) || !Array.isArray(data.nodes))
        throw new Error('unsupported route data');
      return data;
    }).catch(error => { requests.delete(url); throw error; });
    requests.set(url, pending);
  }
  return requests.get(url);
}
