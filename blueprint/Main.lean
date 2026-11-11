import VersoManual
import VersoBlueprint.PreviewManifest
import VersoBlueprint.LeanNamesLegend
import Blueprint

open Verso Doc
open Verso.Genre Manual

-- Review badges are hidden: `--hide-review` is always passed to the generator.
def main (args : List String) : IO UInt32 := do
  -- The explanations of the annotation labels, shown on hovering a label, and their style; every
  -- page inlines both.
  let labelsJs ← IO.FS.readFile "annotation-labels.js"
  let labelsCss ← IO.FS.readFile "annotation-labels.css"
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (Informal.LeanNamesLegend.prepare (htmlDepth := 2) (%doc Blueprint))
    ("--hide-review" :: args)
    (extensionImpls := by exact extension_impls%)
    (config := {
      htmlDepth := 2
      rootTocDepth := some 2
      sectionTocDepth := none
      extraCss := {⟨labelsCss⟩}
      extraJs := {⟨labelsJs⟩} })
