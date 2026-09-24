/* Surface-independent presentation rules. No semantic lookup or lifetime state. */
export function belowSource(rect, popupWidth, viewport) {
  const width = Math.min(popupWidth, viewport.width - 16);
  return {
    left: viewport.scrollX + Math.max(8, Math.min(rect.left, viewport.width - width - 8)),
    top: viewport.scrollY + rect.bottom
  };
}

export function positionBelow(popup, anchor) {
  if (!popup.isConnected || !anchor.isConnected) return;
  const point = belowSource(anchor.getBoundingClientRect(), popup.offsetWidth, {
    width: window.innerWidth, scrollX: window.scrollX, scrollY: window.scrollY
  });
  popup.style.left = point.left + 'px';
  popup.style.top = point.top + 'px';
}

export function clearCodeSelection(scope) {
  scope.querySelectorAll('.expr-active, .name-active, .type-active, .occ').forEach(node => {
    node.classList.remove('expr-active', 'name-active', 'type-active', 'occ');
  });
}
