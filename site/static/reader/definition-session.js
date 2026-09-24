/* Navigation identity and asynchronous lifetime, independent of iframe layout. */
export class DefinitionSession {
  constructor() {
    this.entries = [];
    this.index = -1;
    this.generation = 0;
    this.release = null;
  }
  get current() { return this.entries[this.index] || null; }
  get canBack() { return this.index > 0; }
  get canForward() { return this.index < this.entries.length - 1; }
  push(target, label) {
    this.entries.splice(this.index + 1);
    this.entries.push({target, label});
    this.index = this.entries.length - 1;
    return this.current;
  }
  move(delta) {
    const next = this.index + delta;
    if (next < 0 || next >= this.entries.length) return false;
    this.index = next;
    return true;
  }
  begin() {
    this.invalidate();
    return this.generation;
  }
  isCurrent(generation) { return this.index >= 0 && generation === this.generation; }
  own(release) {
    if (this.release) this.release();
    this.release = release;
  }
  invalidate() {
    this.generation++;
    if (this.release) this.release();
    this.release = null;
  }
  close() {
    this.invalidate();
    this.entries.length = 0;
    this.index = -1;
  }
}
