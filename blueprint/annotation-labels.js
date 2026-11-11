// The label of each annotation box (`aside.bp-editorial`, rendered by VersoBlueprint) explains its
// kind in a popover: on hover and on keyboard focus it shows at once, and a click or a tap keeps
// it open until the next click or tap. `Main.lean` inlines this script in every page.
(() => {
  // One sentence per kind, keyed by the box's `data-kind`. The wording follows "How to read a node"
  // in the appendix (`Blueprint/Conventions.lean`, "Reading the annotations"); keep the two in step.
  const explanations = {
    translation: "A dictionary entry matching a Lean expression with the source's notation or terminology.",
    unformalised: "An item of the source that has no Lean counterpart yet.",
    outOfScope: "An item of the source that has no Lean counterpart, left out by decision.",
    correction: "The source's claim is false as printed, and the Lean statement is a corrected version of it.",
    interpretation: "The source's wording is underspecified, and the Lean statement fixes one reading of it.",
    restatement: "The Lean statement is logically equivalent to the source's statement, in a different form.",
    strengthening: "The Lean statement implies the source's statement.",
    gap: "The Lean statement is weaker than the source's statement, or incomparable with it.",
    meta: "A remark on the formalisation that fits none of the other labels.",
  };

  const LABEL = ".bp-editorial[data-kind] > .bp-editorial-title > .bp-editorial-kind";
  const MARGIN = 8;
  let popover = null;
  let current = null;
  let pinned = false;

  const explanationOf = (label) => explanations[label.closest(".bp-editorial").dataset.kind];

  const prepare = (label) => {
    if (label.classList.contains("bp-kind-help") || !explanationOf(label)) return;
    label.classList.add("bp-kind-help");
    label.tabIndex = 0;
    label.setAttribute("aria-describedby", "bp-kind-popover");
    // The node boxes carry a `title` (the node's label); an empty title on the label keeps the
    // browser from showing it as a second tooltip over the explanation.
    label.title = "";
  };

  const labelAt = (target) => {
    const label = target instanceof Element ? target.closest(LABEL) : null;
    if (!label || !explanationOf(label)) return null;
    prepare(label);
    return label;
  };

  const ensurePopover = () => {
    if (popover) return popover;
    popover = document.createElement("div");
    popover.id = "bp-kind-popover";
    popover.className = "bp-kind-popover";
    popover.setAttribute("role", "tooltip");
    popover.hidden = true;
    document.body.appendChild(popover);
    return popover;
  };

  const show = (label) => {
    const box = ensurePopover();
    current = label;
    box.textContent = explanationOf(label);
    box.style.setProperty("--bp-kind",
      getComputedStyle(label.closest(".bp-editorial")).getPropertyValue("--bp-kind"));
    box.hidden = false;
    place();
  };

  const place = () => {
    const box = popover;
    const label = current;
    // Below the label, left-aligned with it, kept inside the viewport; above it if there is no
    // room below.
    const r = label.getBoundingClientRect();
    const w = box.offsetWidth;
    const h = box.offsetHeight;
    const vw = document.documentElement.clientWidth;
    const vh = window.innerHeight;
    const left = Math.max(MARGIN, Math.min(r.left, vw - w - MARGIN));
    let top = r.bottom + 6;
    if (top + h > vh - MARGIN && r.top - 6 - h >= MARGIN) top = r.top - 6 - h;
    box.style.left = `${left}px`;
    box.style.top = `${top}px`;
  };

  const hide = () => {
    if (popover) popover.hidden = true;
    current = null;
    pinned = false;
  };

  document.addEventListener("pointerover", (e) => {
    if (e.pointerType !== "mouse" || pinned) return;
    const label = labelAt(e.target);
    if (label && label !== current) show(label);
  });
  document.addEventListener("pointerout", (e) => {
    if (e.pointerType !== "mouse" || pinned || !current) return;
    if (labelAt(e.target) === current && !current.contains(e.relatedTarget)) hide();
  });
  document.addEventListener("click", (e) => {
    const label = labelAt(e.target);
    if (!label) {
      if (pinned) hide();
      return;
    }
    if (pinned && label === current) {
      hide();
    } else {
      show(label);
      pinned = true;
    }
  });
  document.addEventListener("focusin", (e) => {
    const label = labelAt(e.target);
    if (label && label !== current) show(label);
  });
  document.addEventListener("focusout", (e) => {
    if (current && e.target === current && !pinned) hide();
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && current) hide();
  });
  window.addEventListener("scroll", () => { if (current) place(); }, { passive: true, capture: true });
  window.addEventListener("resize", () => { if (current) place(); });

  const prepareAll = () => document.querySelectorAll(LABEL).forEach(prepare);
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", prepareAll);
  } else {
    prepareAll();
  }
})();
