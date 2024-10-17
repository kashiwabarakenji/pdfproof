import LLMlean
import Mathlib.Data.Real.Basic

--2項関係と順序 練習5
-- X の上の関係を定義
variable {X : Type} (R : X → X → Prop)

-- Q の定義
def Q (x y : X) : Prop := R x y ∨ x = y

-- 関係 R が推移的であること
variable (trans_R : ∀ ⦃x y z : X⦄, R x y → R y z → R x z)

-- 関係 R が反射的でないこと
variable (not_refl_R : ∀ x : X, ¬R x x)

-- 反射性の証明 (Qは反射的)
theorem Q_refl : ∀ x : X, Q R x x :=
by
  intro x
  -- Q の定義によって、x = x が成立するため反射性が成立
  right
  rfl

-- 反対称性の証明 (Qは反対称的)
theorem Q_antisymm : ∀ {x y : X}, Q R x y → Q R y x → x = y :=
by
  intros x y hxy hyx
  cases hxy with
  | inl rxy =>
    -- xRy が成立する場合
    cases hyx with
    | inl ryx =>
      -- yRx が成立する場合は矛盾
      exfalso

      have := not_refl_R x
      exact this (trans_R rxy ryx)
    | inr rfl =>
      -- y = x が成立する場合は x = y
      rfl
  | inr rfl =>
    -- x = y が成立する場合は x = y
    rfl

-- 推移性の証明 (Qは推移的)
theorem Q_trans : ∀ {x y z : X}, Q R x y → Q R y z → Q R x z :=
by
  intros x y z hxy hyz
  cases hxy with
  | inl rxy =>
    -- xRy が成立する場合
    cases hyz with
    | inl ryz =>
      -- yRz が成立する場合、R の推移性により xRz が成立
      left
      exact trans_R rxy ryz
    | inr rfl =>
      -- y = z の場合、xRz が成立
      left
      exact rxy
  | inr rfl =>
    -- x = y の場合、Q(y, z) の結果は Q(x, z) に対応する
    exact hyz

-- Qが半順序関係であることの証明
theorem Q_is_partial_order : partial_order X (Q R) :=
{
  refl := Q_refl R,
  antisymm := @Q_antisymm X R trans_R not_refl_R,
  trans := @Q_trans X R trans_R
 }
