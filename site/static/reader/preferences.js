/* Storage is optional and isolated per configured textbook instance. */
import { cfg } from './document.js';
export const storageKey = name => `${cfg.storageNamespace || 'textbook'}-${name}`;
export function readPreference(name) {
  try { return localStorage.getItem(storageKey(name)); } catch (_) { return null; }
}
export function writePreference(name, value) {
  try { localStorage.setItem(storageKey(name), value); } catch (_) {}
}
