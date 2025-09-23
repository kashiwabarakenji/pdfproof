--基本的な定義
import Mathlib.Data.Fintype.Basic

noncomputable def finsetInter {α : Type} [DecidableEq α][Fintype α] (A0 : Finset (Finset α)) : Finset α :=
  A0.toList.foldr (fun x acc => x ∩ acc) Finset.univ
