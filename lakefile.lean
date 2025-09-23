import Lake
open Lake DSL

package "pdfproof" where
  -- Settings applied to both builds and interactive editing
    leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
    ]
    --moreLinkArgs := #[
    --  "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    --  "-lctranslate2"
    --]

-- add any additional package configuration options here

require "leanprover-community" / "mathlib" @  "git#v4.23.0"

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.23.0"

@[default_target]
lean_lib «Pdfproof» where
  -- add any library configuration options here
  srcDir := "."
  roots := #[`Pdfproof.set, `Pdfproof.map, `Pdfproof.order,
            `Pdfproof.prop,`Pdfproof.pred,
            `Pdfproof.Lattice.closure_lemma, `Pdfproof.Lattice.lattice_common, `Pdfproof.Lattice.lattice_closure_set, `Pdfproof.Lattice.lattice_closure, `Pdfproof.Lattice.lexorder,`Pdfproof.Lattice.lattice,
            `Pdfproof.zf,`Pdfproof.card,
            `Pdfproof.Dis.dis_func_metric,`Pdfproof.Dis.dis, `Pdfproof.Dis.Ic_OpenPosMeasure,
            `Pdfproof.group,`Pdfproof.homo,`Pdfproof.ring]
