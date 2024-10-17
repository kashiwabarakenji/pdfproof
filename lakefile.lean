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

--require "leanprover-community" / "mathlib" @ "git#20c73142afa995ac9c8fb80a9bb585a55ca38308"
require "leanprover-community" / "mathlib" @  "git#v4.11.0"

--require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.6.0"

require llmlean from git "https://github.com/cmu-l3/llmlean.git" @"main"

@[default_target]
lean_lib «Pdfproof» where
  -- add any library configuration options here
