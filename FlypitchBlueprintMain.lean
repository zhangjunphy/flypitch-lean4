import VersoManual
import VersoBlueprint.PreviewManifest
import FlypitchBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc FlypitchBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)

