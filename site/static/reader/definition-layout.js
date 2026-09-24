/* Explicit reading viewport geometry and canonical target identity. */
function alignModalDefinition(frameDocument, targetBlock) {
  var scroller = frameDocument.getElementById("main-content");
  if (!scroller) return false;
  var scrollerTop = scroller.getBoundingClientRect().top;
  var bar = frameDocument.getElementById("section-sticky");
  /* The retained chapter directory is the only chrome inside the scroller.
     Use its actual edge in the same coordinate system as the target block. */
  var inset = bar ? Math.max(0, bar.getBoundingClientRect().bottom - scrollerTop) : 0;
  var delta = targetBlock.getBoundingClientRect().top - scrollerTop - inset;
  if (Math.abs(delta) <= 0.5) return false;
  var desiredTop = scroller.scrollTop + delta;
  var maximumTop = scroller.scrollHeight - scroller.clientHeight;
  if (desiredTop > maximumTop) {
    var root = frameDocument.documentElement;
    var room = parseFloat(root.style.getPropertyValue("--definition-modal-anchor-room")) || 0;
    root.style.setProperty("--definition-modal-anchor-room",
      Math.ceil(room + desiredTop - maximumTop + 1) + "px");
  }
  /* On iOS Safari the iframe window is not a reliable scrolling element.
     Both the measurement and the write belong to the explicit reading scroller. */
  scroller.scrollTop = desiredTop;
  return true;
}

function sizeModalReadingScroller(frameDocument, modalBody) {
  var scroller = frameDocument.getElementById("main-content");
  if (!scroller) return null;
  /* Use the actual dialog height for the shared desktop/phone reading area. */
  var height = modalBody.clientHeight;
  if (height > 0) {
    frameDocument.documentElement.style.height = height + "px";
    frameDocument.body.style.height = height + "px";
    scroller.style.height = height + "px";
  }
  return scroller;
}

function definitionPageKey(url) {
  var page = new URL(url.href);
  page.hash = "";
  page.searchParams.delete("bedrock-modal");
  page.searchParams.delete("bedrock-modal-scroll");
  page.searchParams.sort();
  /* Static hosts canonicalize .html to extensionless URLs (and index.html
     to a directory). Those redirects still identify the same document. */
  page.pathname = page.pathname.replace(/\/index\.html$/, "/")
    .replace(/\.html$/, "").replace(/\/$/, "") || "/";
  return page.href;
}

export { alignModalDefinition, sizeModalReadingScroller, definitionPageKey };
