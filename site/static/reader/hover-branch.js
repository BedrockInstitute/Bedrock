/* A popup branch has one lifetime regardless of the code surface it came from.
 * No DOM creation, semantic lookup, or navigation belongs in this controller. */
export class HoverBranch {
  constructor({ persistent, clock = globalThis, delay = 360, dispose,
    entered = () => {}, left = () => {} }) {
    this.entries = [];
    this.persistent = persistent;
    this.clock = clock;
    this.delay = delay;
    this.dispose = dispose;
    this.entered = entered;
    this.left = left;
  }
  schedule(callback) {
    if (this.persistent()) return null;
    return this.clock.setTimeout(() => {
      if (!this.persistent()) callback();
    }, this.delay);
  }
  append(entry) { this.entries.push(entry); return entry; }
  removeFrom(index) {
    if (index < 0 || index >= this.entries.length) return false;
    this.entries.splice(index).forEach(entry => {
      this.clock.clearTimeout(entry.closeTimer);
      entry.closeTimer = null;
      this.dispose(entry);
    });
    return true;
  }
  hovered(entry) {
    const index = this.entries.indexOf(entry);
    return index >= 0 && this.entries.slice(index).some(candidate =>
      candidate.anchor.matches(':hover') || candidate.popup.matches(':hover'));
  }
  enter(entry) {
    while (entry) {
      this.clock.clearTimeout(entry.closeTimer);
      entry.closeTimer = null;
      entry = entry.parent;
    }
    this.entered();
  }
  leave(entry) {
    for (let current = entry; current; current = current.parent) {
      this.clock.clearTimeout(current.closeTimer);
      const closing = current;
      current.closeTimer = this.schedule(() => {
        if (this.hovered(closing)) this.enter(closing);
        else this.removeFrom(this.entries.indexOf(closing));
      });
    }
    this.left();
  }
}
