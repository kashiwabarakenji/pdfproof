import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.ModEq
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


theorem infinite_primes : Set.Infinite {p : ℕ | Nat.Prime p} := by
-- 証明の開始：背理法を用いる
-- 「素数の集合が有限である」と仮定し、矛盾を導く
  by_contra h_not_infinite
  -- 「無限ではない」という仮定 h_not_infinite を、
  -- 同値な「有限である」という仮定 h_finite に書き換える
  rw [Set.not_infinite] at h_not_infinite
  let h_finite := h_not_infinite
  -- 有限個の素数をすべて掛け合わせた数 N を定義する
  -- `h_finite.toFinset` は、有限集合を Finset (有限集合の型) に変換する
  let N := ∏ p ∈ h_finite.toFinset, p

  let M := N + 1
  -- M が 1より大きいことを示す (これにより、Mは必ず素因数を持つことが保証される)
  have hM_gt_one : 1 < M := by
  -- Nは素数の積なので、(素数が存在しない場合でも積は 1となり) N > 0 が言える
    suffices 0 < N by exact Nat.lt_add_of_pos_left this
    apply Finset.prod_pos
    -- 積の各要素(素数 p)が正であることを示す
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    exact (hp : Nat.Prime p).pos
  -- M には必ず素因数 q が存在することを利用する
  -- `Nat.minFac` は最小の素因数を返す関数
  let q := Nat.minFac M
  have hq_is_prime : Nat.Prime q := by
    apply Nat.minFac_prime
    simp_all only [lt_add_iff_pos_left, CanonicallyOrderedAdd.prod_pos, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq,
      Nat.add_eq_right, M, N]
    apply Aesop.BuiltinRules.not_intro
    intro a
    rw [Finset.prod_eq_zero_iff] at a
    simp_all only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, exists_eq_right]
    have fwd : False := prime_zero_false a
    clear a
    simp_all only [not_isEmpty_of_nonempty, IsEmpty.forall_iff]
  -- この素因数 q もまた「すべての素数の集合」に含まれているはず
  have hq_in_S : q ∈ {p | Nat.Prime p} := hq_is_prime
  -- 「素数の集合は有限である」という大仮定から、q は h_finite.toFinset の要素でなければならない
  have hq_in_finset : q ∈ h_finite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hq_in_S
  -- 一方、q は M の約数である (Nat.minFac の定義より)
  have hq_div_M : q ∣ M := Nat.minFac_dvd M
  -- また、q は N の約数でもある (qは素数の 1つであり、Nは全ての素数の積だから)
  have hq_div_N : q ∣ N := by
    apply Finset.dvd_prod_of_mem
    exact hq_in_finset

  -- q が M と N の両方を割り切るなら、その差である 1 も割り切れるはず
  have hq_div_one : q ∣ 1 := by
  -- まず、q が M - N を割り切ることを示す
    have h_div_sub := Nat.dvd_sub hq_div_M hq_div_N
    simp [M] at h_div_sub
    exact dvd_one.mpr h_div_sub
  -- 1を割り切る自然数は 1自身のみである
  have h_contradiction : q = 1 := Nat.eq_one_of_dvd_one hq_div_one
  -- これは「qは素数である(つまり 1ではない)」という事実と矛盾する
  -- `hq_is_prime.ne_one` は `q ≠ 1` という証明
  -- これは「qは素数である(つまり 1ではない)」という事実と矛盾する
  exact hq_is_prime.ne_one h_contradiction


namespace IMO2025P3

def IsBonza (f : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b →
    0 < f a ∧ f b * f a ≤ b ^ a ∧ f a ∣ (b ^ a - f b * f a)

/-- 黄金比 `Phi = (1 + √5) / 2` -/
noncomputable def Phi : ℝ := (1 + Real.sqrt 5) / 2

/-- `Phi^2 = Phi + 1` -/
lemma phi_squared : Phi ^ 2 = Phi + 1 := by
  have h5_nonneg : 0 ≤ (5 : ℝ) := by norm_num
  have hsq : (Real.sqrt 5) ^ 2 = 5 := by
    simp

  -- `(x / 2)^2 = x^2 / 4`
  have hdiv :
      ((1 + Real.sqrt 5) / 2) ^ 2
        = ((1 + Real.sqrt 5) ^ 2) / (2 : ℝ) ^ 2 := by
    simpa using div_pow (1 + Real.sqrt 5) (2 : ℝ) (2 : ℕ)
  have h2sq : (2 : ℝ) ^ 2 = 4 := by norm_num
  have : Phi ^ 2 = ((1 + Real.sqrt 5) ^ 2) / 4 := by
    unfold Phi
    simpa [h2sq] using hdiv
  calc
    Phi ^ 2
        = ((1 + Real.sqrt 5) ^ 2) / 4 := this
    _   = (1 + 2 * Real.sqrt 5 + (Real.sqrt 5) ^ 2) / 4 := by ring
    _   = (1 + 2 * Real.sqrt 5 + 5) / 4 := by simp [hsq]
    _   = (6 + 2 * Real.sqrt 5) / 4 := by ring
    _   = (2 * (3 + Real.sqrt 5)) / 4 := by ring
    _   = (3 + Real.sqrt 5) / 2 := by
       simp_all only [Nat.ofNat_nonneg, Real.sq_sqrt]
       ring
    _   = ((1 + Real.sqrt 5) / 2) + 1 := by ring
    _   = Phi + 1 := by rfl

/-- `Phi > 0` -/
lemma phi_pos : 0 < Phi := by
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    have : 0 < (5 : ℝ) := by norm_num
    simp
  have hnum_pos : 0 < 1 + Real.sqrt 5 := by
    have : 0 < (1 : ℝ) := by norm_num
    have := add_pos_of_pos_of_nonneg this (le_of_lt hsqrt_pos)
    -- 上の `this` は `0 < 1 + √5` を直接は与えないので、素直に `linarith` で。
    linarith
  have hden_pos : 0 < (2 : ℝ) := by norm_num
  simpa [Phi] using div_pos hnum_pos hden_pos

/-- `a=1` を代入した bonza 条件。 -/
lemma bonza_at_a_one (f : ℕ → ℕ) (hf : IsBonza f) (b : ℕ) (hb : 0 < b) :
    0 < f 1 ∧ f b * f 1 ≤ b ^ 1 ∧ f 1 ∣ (b ^ 1 - f b * f 1) := by
  simpa using hf 1 b (by decide) hb

/-- `b=1` を代入した bonza 条件。 -/
lemma bonza_at_one (f : ℕ → ℕ) (hf : IsBonza f) (a : ℕ) (ha : 0 < a) :
    0 < f a ∧ f 1 * f a ≤ 1 ^ a ∧ f a ∣ (1 ^ a - f 1 * f a) := by
  simpa using hf a 1 ha (by decide)

/-- 任意の bonza 関数は `f 1 = 1` を満たす。 -/
lemma bonza_f_one (f : ℕ → ℕ) (hf : IsBonza f) : f 1 = 1 := by
  -- `a=1, b=1` の場合
  have h := bonza_at_a_one f hf 1 (by decide)
  have hpos : 0 < f 1 := h.left
  have hle : f 1 * f 1 ≤ 1 := by
    -- `b ^ 1 = b` を使う
    simpa [Nat.pow_one] using h.right.left
  -- 乗法の 1 以下からそれぞれが 1 以下
  have hle' := by exact hf (f 1) (f 1) hpos hpos--Nat.mul_le_one.mp hle
  have hle1 : f 1 ≤ 1 := by exact Nat.mul_self_le_mul_self_iff.mp hle--hle'.left
  have hge1 : 1 ≤ f 1 := Nat.succ_le_of_lt hpos
  exact Nat.le_antisymm hle1 hge1

/-- 任意の bonza 関数は粗い上界 `f n ≤ n` を満たす。 -/
lemma bonza_le_id (f : ℕ → ℕ) (hf : IsBonza f) (n : ℕ) (hn : 0 < n) :
    f n ≤ n := by
  have h := bonza_at_a_one f hf n hn
  have f1eq : f 1 = 1 := bonza_f_one f hf
  -- `f n * f 1 ≤ n ^ 1` を `f n ≤ n` に落とす
  have : f n * 1 ≤ n := by
    simpa [f1eq, Nat.pow_one] using h.right.left
  simpa using this

/-- フィボナッチ数列 -/
def fib : ℕ → ℕ
  | 0       => 0
  | 1       => 1
  | n + 2   => fib (n + 1) + fib n

@[simp] lemma fib_zero : fib 0 = 0 := rfl
@[simp] lemma fib_one  : fib 1 = 1 := rfl
@[simp] lemma fib_succ_succ (n : ℕ) : fib (n + 2) = fib (n + 1) + fib n := rfl

/-- 基本補題：`∀ n, 0 < fib (n+1)`。 -/
lemma fib_succ_pos (n : ℕ) : 0 < fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- `fib (n+2) = fib (n+1) + fib n` と `ih : 0 < fib (n+1)` から従う
      have h : 0 < fib (n + 1) + fib n := Nat.add_pos_left ih _
      simpa [fib_succ_succ] using h

/-- `n > 0` なら `fib n > 0`。 -/
lemma fib_pos {n : ℕ} (hn : 0 < n) : 0 < fib n := by
  cases n with
  | zero => cases hn
  | succ m =>
      simpa using fib_succ_pos m

end IMO2025P3

-- === ステップ 1: 「数」の定義 (ペアノの公理) ===
--
-- `MyNat` という新しい型（タイプ）を定義します。
-- `MyNat` の値は、以下の 2種類のどちらかです。
inductive MyNat where
  | zero : MyNat                 -- 1. `zero` (0のこと)
  | succ (n : MyNat) : MyNat     -- 2. `succ n` (n の「次の数」、n+1 のこと)

-- `MyNat` の 0, 1, 2 を使いやすいように定義しておきます
def zero : MyNat := MyNat.zero
def one  : MyNat := MyNat.succ zero
def two  : MyNat := MyNat.succ one

-- === ステップ 2: 「足し算」の定義 ===
--
-- `my_add n m` (n + m のこと) を定義します。
-- 2番目の引数 `m` の形によって、再帰的に定義します。
def MyNat.my_add : MyNat → MyNat → MyNat
  | n, MyNat.zero     => n                             -- ケース 1: n + 0 = n (これは定義)
  | n, MyNat.succ k   => by
    apply MyNat.succ
    exact my_add n k                             -- ケース 2: n + (k + 1) = (n + k) + 1

-- `+` の代わりに `my_add`、`0` の代わりに `zero` を使います。
-- これで準備完了です。

-- === 練習問題 (証明は `sorry` になっています) ===

-- 定理 1: `0 + n = n`
-- ★ `def zero` ではなく `MyNat.zero` を使って書き直します
theorem MyNat.zero_add (n : MyNat) : my_add MyNat.zero n = n := by
  induction n with
  | zero =>
      -- ゴール: my_add MyNat.zero MyNat.zero = MyNat.zero
      rw [my_add]
  | succ k ih =>
      -- ゴール: my_add MyNat.zero (MyNat.succ k) = MyNat.succ k
      rw [my_add]        -- 'my_add n (succ k) => ...' の定義が左辺に適用される
      rw [ih]            -- 'my_add MyNat.zero k' を 'k' に書き換える

-- 定理 2: `(n + 1) + m = (n + m) + 1`
theorem MyNat.succ_add (n m : MyNat) : my_add (MyNat.succ n) m = MyNat.succ (my_add n m) := by
  -- m についての `induction` で証明できます
  induction m with
  | zero =>
      rfl
  | succ k ih =>
      rw [my_add]
      rw [ih]
      simp
      rfl

-- 定理 3 (挑戦): 足し算の交換法則 `n + m = m + n`
theorem MyNat.add_comm (n m : MyNat) : my_add n m = my_add m n := by
  -- n についての `induction`
  induction n with
  | zero =>
      rw [my_add]
      apply MyNat.zero_add
  | succ k ih =>
      rw [my_add]
      rw [succ_add]
      rw [ih]

-- === ステップ 3: 「掛け算」の定義 ===
--
-- `my_mul n m` (n * m のこと) を定義します。
-- `my_add` (足し算) を使って、再帰的に定義します。
def MyNat.my_mul : MyNat → MyNat → MyNat
  | _, MyNat.zero    => MyNat.zero                  -- ← 'n' を '_' に変更
  | n, MyNat.succ k  => my_add (my_mul n k) n       -- ← 2行目は 'n' を使うのでそのまま

-- === ステップ 4: 残りの定理 (証明は `sorry`) ===

-- 4. 足し算の結合法則 ((n + m) + k = n + (m + k))
-- (これは掛け算の証明の途中でよく使います)
theorem MyNat.add_assoc (n m k : MyNat) :
    my_add (my_add n m) k = my_add n (my_add m k) := by
  induction n with
  | zero =>
      rw [zero_add]
      rw [zero_add]
  | succ l ih =>
      rw [succ_add]
      rw [succ_add]
      rw [ih]
      rw [succ_add]

-- 5. 掛け算の左ゼロ元 (0 * n = 0)
theorem MyNat.zero_mul (n : MyNat) : my_mul MyNat.zero n = MyNat.zero := by
  induction n with
  | zero =>
      rw [my_mul]
  | succ k ih =>
      rw [my_mul]
      rw [ih]
      rw [my_add]

-- 6. 左分配法則 (n * (m + k) = n * m + n * k)
theorem MyNat.left_distrib (n m k : MyNat) :
    my_mul n (my_add m k) = my_add (my_mul n m) (my_mul n k) := by
  -- ★★★ n ではなく k で induction します ★★★
  induction k with
  | zero =>
      rw [my_add]
      rw [my_mul]
      rw [my_add]
  | succ l ih =>
      rw [my_add]
      rw [my_mul]
      rw [ih]
      rw [my_mul]
      rw [add_assoc]

-- 7. 右分配法則 ((n + m) * k = n * k + m * k)
theorem MyNat.right_distrib (n m k : MyNat) :
    my_mul (my_add n m) k = my_add (my_mul n k) (my_mul m k) := by
  induction k with
  | zero =>
      rw [my_mul]
      rw [my_mul]
      rw [my_mul]
      rw [my_add]
  | succ l ih =>
      simp [my_mul]
      rw [ih]
      rw [add_assoc]
      rw [add_assoc]
      rw [← add_assoc (my_mul m l) n m]
      -- 3. `B + C` が隣り合ったので、交換します
      -- `(B + C) + D` -> `(C + B) + D`
      rw [add_comm (my_mul m l) n]
      -- 4. カッコを元に戻します
      -- `(C + B) + D` -> `C + (B + D)`
      rw [add_assoc n (my_mul m l) m]

-- 補助定理: (n+1) * m = (n*m) + m
theorem MyNat.succ_mul (n m : MyNat) :
    my_mul (MyNat.succ n) m = my_add (my_mul n m) m := by
  -- m についての induction
  induction m with
  | zero =>
      rw [my_mul]
      rw [my_mul]
      rw [my_add]
  | succ k ih =>
      rw [my_mul]
      rw [ih]
      rw [my_add]
      rw [my_mul]
      rw [add_comm]
      rw [my_add]
      rw [add_assoc]
      rw [add_comm n k]
      rw [add_comm n (my_add (my_mul n k) k)]
      rw [add_assoc]

-- 8. 掛け算の交換法則 (n * m = m * n)
-- ★これが次の大きな目標です
theorem MyNat.mul_comm (n m : MyNat) : my_mul n m = my_mul m n := by
  -- `right_distrib` や `zero_mul` などが必要です
  induction n with
  | zero =>
      rw [my_mul]
      rw [zero_mul]
  | succ k ih =>
      rw [my_mul]
      rw [succ_mul]
      rw [ih]

-- 9. 掛け算の結合法則 ((n * m) * k = n * (m * k))
theorem MyNat.mul_assoc (n m k : MyNat) :
    my_mul (my_mul n m) k = my_mul n (my_mul m k) := by
  induction n with
  | zero =>
      rw [zero_mul]
      rw [zero_mul]
      rw [zero_mul]
  | succ l ih =>
      rw [succ_mul]
      rw [right_distrib]
      rw [ih]
      rw [succ_mul]

---------

theorem square_condition_implies_n_le_a (a n : ℕ) (ha : 1 ≤ a) --(hn : 1 ≤ n)
(h : ∃ k : ℕ, n^2 + n - a = k^2) : n ≤ a := by
  obtain ⟨k, hk⟩ := h
  by_contra hna
  push_neg at hna
  have h1 : a < n := hna
  have h2 : n^2 + n = k^2 + a := by
   omega
  cases' le_or_gt k n with hkn hkn
  · nlinarith
  · have h3 : k ≥ n + 1 := Nat.succ_le_of_lt hkn
    nlinarith

theorem Add_comm (a b : Nat) : a + b = b + a := by
induction b with
| zero =>
  rw [Nat.add_zero, zero_add]
| succ b ih =>
  rw [Nat.add_succ, ih, Nat.succ_add]

theorem Add_comm_nat (a b : ℕ) : a + b = b + a := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    exact Add_comm (a + 1) b
