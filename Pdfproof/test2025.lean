import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic
import LeanCopilot
open Int
open Nat

-- 論理式 (A → (A → B)) → (A → B) の証明
example (A B : Prop) : (A → (A → B)) → (A → B) := by
  -- 1. 仮定 h1 : A → (A → B) を導入（全体の式の →I）
  intro h1 h2
  -- 2. 仮定 h2 : A を導入（A → B の →I）
  -- ゴール：B
  -- 3. h1 と h2 から A → B を得る（→E）
  have h3 : A → B := h1 h2
  -- 4. h3 と h2 から B を得る（→E）
  exact h3 h2


namespace Tokyo2024Q6
def f (n : Int) : Int := n^3 + 10 * n^2 + 20 * n

theorem part1 :
∀ n : Int,
Nat.Prime (f n).natAbs ↔ (n = 1 ∨ n = -1 ∨ n = -3 ∨ n = -7) :=
by
    intro n
    constructor
    -- → 方向（素数なら候補に絞る）
    · intro h_prime
    -- f(n) = n*(n^2+10n+20)

      have h_fact : f n = n * (n^2 + 10*n + 20) := by
        unfold f
        ring
      -- n = 0 の場合は素数にならない
      have h_n0 : n ≠ 0 := by
        intro h; rw [h_fact, h] at h_prime;
        norm_num at h_prime
        -- n | f(n) かつ f(n) は素数なので n = ±1 または n^2+10n+20 = ±1
      have h_prod :
        (f n).natAbs
          = (Int.natAbs n) * (Int.natAbs (n^2 + 10*n + 20)) := by
        have := congrArg Int.natAbs h_fact
        -- `natAbs (a*b) = natAbs a * natAbs b`
        simpa [Int.natAbs_mul]
      have h_dvd_n :
        (Int.natAbs n) ∣ (f n).natAbs := by
        rw [h_prod]; exact Nat.dvd_mul_right _ _
      have h_dvd_t :
          (Int.natAbs (n^2 + 10*n + 20)) ∣ (f n).natAbs := by
        rw [h_prod]; exact Nat.dvd_mul_left _ _


      have hn_cases := Nat.Prime.eq_one_or_self_of_dvd h_prime (Int.natAbs n) h_dvd_n
    -- 4分岐： n=±1 または |n|=(f n).natAbs（このとき |t|=1 を導出）
      have h_cases :
        n = 1 ∨ n = -1 ∨ n^2 + 10*n + 20 = 1 ∨ n^2 + 10*n + 20 = -1 := by
        cases hn_cases with
        | inl h_abs_n_one =>
            -- |n| = 1 → n = ±1
            have := (Int.natAbs_eq_iff.mp h_abs_n_one)
            cases this with
            | inl h => exact Or.inl h
            | inr h => exact Or.inr (Or.inl h)
        | inr h_abs_n_eq_p =>
            -- |n| = |f n| ⇒ |f n| = |n| * |t| より |t| = 1
            -- まず |t| = 1 を得る
            have h_eq : (f n).natAbs = (Int.natAbs n) * (Int.natAbs (n^2 + 10*n + 20)) := h_prod
            -- p = p * |t| なので左から約すれば |t| = 1
            have hp_pos : 0 < (f n).natAbs :=
              Nat.lt_trans Nat.zero_lt_one (Nat.Prime.one_lt h_prime)
            have ht_one : Int.natAbs (n^2 + 10*n + 20) = 1 := by
              --  p = p * |t|  →  p*1 = p*|t|  →  1 = |t|
              have : (f n).natAbs = (f n).natAbs * (Int.natAbs (n^2 + 10*n + 20)) := by
                -- 置換して整理
                -- |n| = |f n| を使う
                have : (f n).natAbs = (Int.natAbs n) := by exact id (Eq.symm h_abs_n_eq_p)
                -- これと h_eq を併用
                -- 最終的に `p = p * |t|`
                simpa [this] using h_eq
              have : (f n).natAbs * 1
                    = (f n).natAbs * (Int.natAbs (n^2 + 10*n + 20)) := by
                simpa [Nat.mul_one] using this
              exact
                (Nat.mul_left_cancel hp_pos this).symm
            -- |t| = 1 → t = ±1
            have := Int.natAbs_eq_iff.mp ht_one
            cases this with
            | inl h => exact Or.inr (Or.inr (Or.inl h))
            | inr h => exact Or.inr (Or.inr (Or.inr h))

      -- （ここにあなたの “t=-1 ⇒ n=-3∨n=-7” の証明を入れる）

      cases h_cases with
      | inl h => exact Or.inl h -- n = 1
      | inr h1 => cases h1 with
        | inl h => exact Or.inr (Or.inl h) -- n = -1
        | inr h2 => cases h2 with
          | inl h => -- ケース: n^2 + 10*n + 20 = 1
            -- n^2 + 10*n + 19 = 0
            -- (n + 5)^2 - 25 + 19 = 0
            -- (n + 5)^2 = 6
            -- 整数解なし -> 矛盾
            exfalso
            have h_poly : n ^ 2 + 10 * n + 19 = 0 := by linarith [h]
            -- (n + 5)^2 = 6 を導出
            have h_complete_sq : (n + 5) ^ 2 = 6 := by
              calc (n + 5) ^ 2
                _ = n ^ 2 + 10 * n + 25 := by ring
                _ = (n ^ 2 + 10 * n + 19) + 6 := by ring
                _ = 0 + 6 := by rw [h_poly]
                _ = 6 := by ring
            -- (n + 5).natAbs ^ 2 = 6
            have h_abs_sq : (n + 5).natAbs ^ 2 = 6 := by
              dsimp [Int.natAbs]
              let ca := congrArg Int.natAbs h_complete_sq
              simp [pow_two,]
              have h1 : Int.natAbs (n + 5) * Int.natAbs (n + 5) = 6 := by
                -- 左辺を展開：|(n+5)^2| = |(n+5)*(n+5)| = |n+5|*|n+5|
                have h0 := ca
                rw [pow_two, Int.natAbs_mul] at h0
                -- 右辺：|6| = 6
                have habs6 : Int.natAbs (6 : Int) = 6 := Int.natAbs_natCast 6
                rw [habs6] at h0
                exact h0

              -- ゴールの LHS は `Int.natAbs (n+5)` の定義展開なので、目標を畳み直す
              change Int.natAbs (n + 5) * Int.natAbs (n + 5) = 6
              exact h1

            let k := (n + 5).natAbs
            have h_k : k ^ 2 = 6 := h_abs_sq
            -- k (自然数) の場合分けで矛盾を導く
            cases k0:k with
            | zero => simp_all only [mul_one, ne_eq, isUnit_one, natAbs_of_isUnit, dvd_refl, isUnit_iff_eq_one, IsUnit.dvd, or_true,
               natAbs_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, OfNat.zero_ne_ofNat, k]

            | succ k' =>
              cases k1:k' with
              | zero =>
                  subst k1
                  simp_all only [mul_one, ne_eq, isUnit_one, natAbs_of_isUnit, dvd_refl, isUnit_iff_eq_one, IsUnit.dvd, or_true,
                    zero_add, one_pow, OfNat.one_ne_ofNat, k]

              | succ k'' =>
                cases k2:k'' with
                | zero =>
                  subst k1 k2
                  simp_all only [mul_one, ne_eq, isUnit_one, natAbs_of_isUnit, dvd_refl, isUnit_iff_eq_one, IsUnit.dvd, or_true,
                    zero_add, Nat.reduceAdd, Nat.reducePow, reduceEqDiff, k]

                | succ k''' => -- k >= 3
                  have h_k_ge_3 : k ≥ 3 := by
                    subst k2 k1
                    simp_all only [mul_one, ne_eq, isUnit_one, natAbs_of_isUnit, dvd_refl, isUnit_iff_eq_one, IsUnit.dvd, or_true,
                      ge_iff_le, le_add_iff_nonneg_left, _root_.zero_le, k]


                  have h_k2_ge_9 : k ^ 2 ≥ 3 ^ 2 := Nat.pow_le_pow_left h_k_ge_3 2
                  rw [h_k] at h_k2_ge_9 -- 6 ≥ 9
                  norm_num at h_k2_ge_9 -- False

          | inr h => -- ケース: n^2 + 10*n + 20 = -1
            -- n^2 + 10*n + 21 = 0
            -- (n + 3)(n + 7) = 0
            -- n = -3 または n = -7
            have h_poly : n ^ 2 + 10 * n + 21 = 0 := by linarith [h]
            have h_fact_poly : (n + 3) * (n + 7) = 0 := by
              rw [← h_poly]; ring
            -- 積が0なので、どちらかの因子が0
            have h_zero_prod := Int.mul_eq_zero.mp h_fact_poly
            cases h_zero_prod with
            | inl h_n3 => -- n + 3 = 0
              have h_n_eq_m3 : n = -3 := by linarith [h_n3]
              exact Or.inr (Or.inr (Or.inl h_n_eq_m3))
            | inr h_n7 => -- n + 7 = 0
              have h_n_eq_m7 : n = -7 := by linarith [h_n7]
              exact Or.inr (Or.inr (Or.inr h_n_eq_m7))

    -- ← 方向（候補を直接評価）
    · intro h_or
      cases h_or with
      | inl h => rw [h]; unfold f; norm_num -- n = 1, f(n) = 31
      | inr h1 => cases h1 with
      | inl h => rw [h]; unfold f; norm_num -- n = -1, f(n) = 9
      | inr h2 => cases h2 with
      | inl h => rw [h]; unfold f; norm_num -- n = -3, f(n) = 3
      | inr h => rw [h]; unfold f; norm_num -- n = -7, f(n) = 7
end Tokyo2024Q6

example (a b : Nat) (h : a = b) :
  a + 1 = b + 1 := by
   rw [h]

example {α : Type} {P: α → Prop}:
¬(∃x, P x) → ∀x,
¬(P x) := by
intro a x
rw [not_exists] at a --既存定理をそのまま利用して証明。

exact a x

example {α : Type} {P : α → Prop} :
¬(∃ x, P x) → ∀ x,
¬(P x) := by
  intro h x px
  --ここでゴールは、
  --(P x)。これはP(x) → Falseと思える。
  -- px：P xとなり、goalがFalseになる。
  have ex : ∃ x, P x := ⟨x, px⟩ --補題を証明してexと命名
  exact h ex -- ¬A A の順で並べることで矛盾Falseが得られる。

example {α : Type} (A B C : Set α) :
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
ext x --要素が含まれるかの議論に変換。
--goal x ∈ A ∩ (B ∪ C) ↔ x ∈ A ∩ B ∪ A ∩ C
simp only [Set.mem_inter_iff, Set.mem_union]

--import Mathlib.Data.Set.Basicが必要
apply Iff.intro --左から右の証明と右から左の証明に分解
· intro a --左から右。goal: x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
  cases a with
  | intro hA hBC => --hA : x ∈ A, hBC : x ∈ B ∨ x ∈ C
  cases hBC with
  | inl hB => exact Or.inl ⟨hA, hB⟩ --hB : x ∈ B
  | inr hC => exact Or.inr ⟨hA, hC⟩ --hC : x ∈ C
· intro a --右から左。goal: x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
  cases a with
  | inl h => simp_all only [true_or, and_self]
  | inr h_1 => simp_all only [or_true, and_self]

example {α β : Type}  (f : α → β) :
 (∀ A : Set α, (f '' A)ᶜ ⊆ f '' (Aᶜ)  )
  → Function.Surjective f := by
  intro h
  rw [Function.Surjective]
  by_contra hns
  push_neg at hns
  obtain ⟨y, hy⟩ := hns
  have h1 : y ∈ (f '' Set.univ)ᶜ := by
    simp_all only [ne_eq, Set.image_univ, Set.mem_compl_iff,
    Set.mem_range, exists_false,not_false_eq_true]
  have h2 : y ∉ f '' (Set.univᶜ) := by
    simp_all only [ne_eq, Set.image_univ, Set.mem_compl_iff,
    Set.mem_range, exists_false,not_false_eq_true,
    Set.compl_univ, Set.image_empty, Set.mem_empty_iff_false]
  exact h2 (h Set.univ h1)
