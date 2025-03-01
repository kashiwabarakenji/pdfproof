import Lake
open Lake DSL

package "pdfproof" where
  -- Settings applied to both builds and interactive editing
    leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
    ]
    moreLinkArgs := #[
      "-L./.lake/packages/LeanCopilot/.lake/build/lib",
      "-lctranslate2"
    ]

-- add any additional package configuration options here

require "leanprover-community" / "mathlib" @  "git#v4.16.0"

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.16.0"

@[default_target]
lean_lib «Pdfproof» where
  -- add any library configuration options here
  srcDir := "."
  roots := #[`Pdfproof.lattice_common, `Pdfproof.lattice_closure_set, `Pdfproof.lattice_closure,  `Pdfproof.dis_func_metric, `Pdfproof.Ic_OpenPosMeasure]
