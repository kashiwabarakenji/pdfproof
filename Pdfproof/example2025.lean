import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic
import LeanCopilot

set_option maxRecDepth 10000

open Finset
open Int
open scoped BigOperators

open Finset
open scoped BigOperators

theorem sum_of_first_n (n : ℕ) :
    ∑ k ∈ range (n + 1), k = n * (n + 1) / 2 := by
  classical
  -- ∑_{k=0}^{n} k = (n+1)*n/2 を利用して、掛け算の順序だけ入れ替える
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc
      ∑ k ∈ range (n + 2), k
          = ∑ k ∈ range (n + 1), k + (n + 1) := by rw [Finset.sum_range_succ]
      _ = n * (n + 1) / 2 + (n + 1) := by rw [ih]
      _ = (n + 1) * (n + 2) / 2 := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        ring_nf
        omega

----フェルマーの小定理-----
open Nat ZMod
-- 補題：a, 2a, ..., (p-1)a を p で割った余りはすべて異なる
theorem distinct_multiples_of_coprime_mod_prime
(p : ℕ) (hp : p.Prime) (a : ℕ) (h_coprime : a.Coprime p) :
∀ i j : Fin (p - 1),
(i : ℕ) ≠ (j : ℕ) →
¬ (((i : ℕ) + 1) * a ≡ ((j : ℕ) + 1) * a [MOD p]) := by
  intro i j h_ne h_eq
  -- ZMod p の世界に持ち込む
  let i_nat := (i : ℕ) + 1
  let j_nat := (j : ℕ) + 1
  let a_mod : ZMod p := a
  -- congruence を ZMod 上の等式に変換
  have h_mul_eq : ((i_nat : ZMod p) * a_mod) = ((j_nat : ZMod p) * a_mod) := by
  -- Nat.ModEq a b [MOD p] から (a : ZMod p) = (b : ZMod p) を得る
    have h' : ((i_nat * a : ℕ) : ZMod p) = (j_nat * a : ℕ) := by
      simp only [Nat.ModEq] at h_eq
        -- h_eq は (i_nat * a) % p = (j_nat * a) % p
      have : ((i_nat * a) % p : ZMod p) = ((j_nat * a) % p : ZMod p) := by rw [h_eq]
      simp only [ZMod.natCast_mod] at this
      exact this
    simpa [a_mod] using h'
  have h_a_unit : IsUnit (a_mod : ZMod p) := by

  -- 1. hp (Nat.Prime p) から [Fact p.Prime] インスタンスを作成
  -- これにより ZMod.instField が有効になり、ZMod p が体(Field)として認識される
    haveI : Fact p.Prime := ⟨hp⟩
  -- 2. a_mod ≠ 0 を先に証明する
    have h_ne_zero : a_mod ≠ 0 := by
      unfold a_mod
      -- Goal: (↑a : ℕ) ≠ 0
      -- 1. Ne で `≠` を `¬` に展開
      -- 2. natCast_eq_zero_iff a で `↑a = 0` を `p ∣ a` に書き換え
      -- 3. [← hp.coprime_iff_not_dvd] で `¬(p ∣ a)` を `p.Coprime a` に逆書き換え
      rw [Ne, natCast_eq_zero_iff a, ← hp.coprime_iff_not_dvd]
      -- Goal: p.Coprime a
      -- a.Coprime p (h_coprime) と p.Coprime a は Nat.Coprime.comm により同じ
      exact h_coprime.symm
  -- 3. ZMod p は体であり、h_ne_zero (a_mod ≠ 0) の証明があるので、
  -- Units.mk0 を使って単元(Units)を構築し、.isUnit で IsUnit の証明を得る
    exact (Units.mk0 a_mod h_ne_zero).isUnit
  -- 単元なのでキャンセルできる
  have h_cancel : (i_nat : ZMod p) = (j_nat : ZMod p) :=
  IsUnit.mul_right_cancel h_a_unit h_mul_eq
  -- p より小さいことを確認
  have h_lt : i_nat < p ∧ j_nat < p := by
    constructor
    · calc
      i_nat = (i : ℕ) + 1 := rfl
      _
      < (p - 1) + 1 := Nat.add_lt_add_right (Fin.is_lt i) 1
      _
      = p := Nat.sub_add_cancel (hp.one_lt.le)
    · calc
      j_nat = (j : ℕ) + 1 := rfl
      _
      < (p - 1) + 1 := Nat.add_lt_add_right (Fin.is_lt j) 1
      _
      = p := Nat.sub_add_cancel (hp.one_lt.le)
    -- ZMod の等式から自然数の等式へ
  have h_nat_eq : i_nat = j_nat := by
  -- 1. ZMod p 上で等しいなら、その .val (0～p-1 の値) も等しい
    have h_val_eq : (i_nat : ZMod p).val = (j_nat : ZMod p).val := by
      rw [h_cancel]
      -- 2. (n : ZMod p).val は n % p と等しい、という定理 (val_natCast) を使う

      -- (open ZMod されているため ZMod. プレフィックス不要)
    rw [val_natCast, val_natCast] at h_val_eq
    -- Goal: i_nat % p = j_nat % p
    -- 3. i_nat < p かつ j_nat < p (h_lt) を使う
    -- Nat.mod_eq_of_lt (a < b → a % b = a) を適用
    rw [Nat.mod_eq_of_lt h_lt.1] at h_val_eq
    rw [Nat.mod_eq_of_lt h_lt.2] at h_val_eq
    -- Goal: i_nat = j_nat
    -- 4. ゴールそのものが得られた
    exact h_val_eq
  have h_eq_i_j : (i : ℕ) = (j : ℕ) :=
  Nat.succ_injective h_nat_eq
  contradiction
  def main : IO Unit := do
  IO.println "Fermat's Little Theorem sublemma proved."

------
--import Mathlib.Data.Nat.Parity -- 偶数・奇数の定義を含むライブラリをインポート
-- 命題: n^2 が偶数ならば n も偶数である
theorem even_of_even_sq (n : ℕ) (h_even_sq : Even (n^2)) : Even n := by
  by_contra hn_odd
  simp at hn_odd
  obtain ⟨k, hk⟩ := hn_odd
  have : Odd (n^2) := by
    have :∃ m : ℕ, n^2 = 2 * m + 1 := by
      use 2 * k * k + 2 * k
      calc
        n^2 = (2 * k + 1)^2 := by rw [hk] -- n を 2k + 1 に置き換え
          _ = 4 * k^2 + 4 * k + 1 := by ring -- 展開
          _ = 2 * (2 * k^2 + 2 * k) + 1 := by ring -- 2 でくくる
          _ = 2 * (2 * k * k + 2 * k) + 1 := by ring -- より⼀般的な形
    exact this
  cases h_even_sq with
  | intro m h_eq =>
    simp_all only
    obtain ⟨x, hx⟩ := this
    simp_all only
    omega

---

example (n : ℕ) : ∃ m : ℕ, n ^ 2 - n = 2 * m := by
by_cases n_even : Even n
· -- n が偶数の時
  obtain ⟨k, hk⟩ := n_even
  rw [hk]
  use (2 * k^2 - k)
  calc
  (k + k) ^ 2 - (k + k)
  _ = (2 * k) ^ 2 - (2 * k) := by ring_nf
  _ = 4 * k^2 - 2 * k := by ring_nf
  _ = 2 * (2 * k^2 - k) := by omega
· -- n が奇数の時
  -- 奇数証人を自前で作る（Nat.* を使わない）
  have : ∃ k, n = 2 * k + 1 := by
  -- 簡易な構成：n をパターン分解
    cases n with
    | zero =>
    -- n = 0 なら ¬Even n が矛盾（偶数そのもの）なのでこの枝は到達しない
    exact (n_even ⟨0, by simp⟩).elim
    | succ tt =>
    -- n = t+1。もし t が偶数なら t+1 は 2k+1 の形、そうでなくても t+1 は 2k+1 の形
    -- ここは “2k+1 の形”の存在を直接提示する：
      simp at n_even
      obtain ⟨t, ht⟩ := n_even
      use t
  obtain ⟨k, hk⟩ := this
  --n(n-1)/2をmとして入れる。
  --(2*k+1)(2*k)/2=(2*k+1)*k
  use (2 * k + 1) * k
  rw [hk]
  simp_all only [not_even_bit1, not_false_eq_true]
  ring_nf
  omega

---
/-- 基本の因数分解：整数環上で `n^9 - n^3` を因数分解する -/
lemma factor (n : ℤ) :
    n^9 - n^3 = n^3 * (n - 1) * (n^2 + n + 1) * (n + 1) * (n^2 - n + 1) := by
  ring

lemma three_dvd_quadratic_pos (n : ℤ) (h1 : n ≡ 1 [ZMOD 3]) :
    3 ∣ n^2 + n + 1 := by
  -- n² + n + 1 ≡ 0 mod 3 を示す
  have : (n^2 + n + 1 : ℤ) ≡ 0 [ZMOD 3] := by
    calc
      n^2 + n + 1 ≡ 1^2 + 1 + 1 [ZMOD 3] := by
        apply Int.ModEq.add (Int.ModEq.add (h1.pow 2) h1) (Int.ModEq.refl 1)
      _ = 3 := by norm_num
      _ ≡ 0 [ZMOD 3] := by decide
  exact Int.modEq_zero_iff_dvd.mp this

lemma lem1 (n : ℤ) (h1 : n ≡ -1 [ZMOD 3]) : n ^ 2 - n + 1 ≡ 0 [ZMOD 3] := by
  calc
    n ^ 2 - n + 1 ≡ (-1) ^ 2 - (-1) + 1 [ZMOD 3] := by
      -- h1 を使って n を -1 に置き換える
      apply Int.ModEq.add (Int.ModEq.sub (h1.pow 2) h1) (Int.ModEq.refl 1)
    _ = 1 + 1 + 1 := by ring  -- (-1)^2 = 1, -(-1) = 1 なので 1 + 1 + 1
    _ = 3 := by norm_num
    _ ≡ 0 [ZMOD 3] := by decide  -- 3 ≡ 0 mod 3

/-- 補題：`n ≡ -1 [ZMOD 3]` なら `3 ∣ n^2 - n + 1` -/
lemma three_dvd_quadratic_neg (n : ℤ) (h1 : n ≡ (-1 : ℤ) [ZMOD 3]) :
    3 ∣ n^2 - n + 1 := by
  -- 3 で割った余りで評価すると (-1)^2 - (-1) + 1 = 1 + 1 + 1 = 3 ≡ 0
  have : (n^2 - n + 1 : ℤ) ≡ 0 [ZMOD 3] := by
    -- `n^2 - n + 1` は `n^2 + (-n) + 1`
    have h₂ := (h1.pow 2)
    --have h₁ := h1.neg_right -- `-n ≡ 1 [ZMOD 3]`
    -- それぞれを代入
    exact lem1 n h1
  exact dvd_of_emod_eq_zero this


/-- 主定理：任意の整数 `n` について `9 ∣ n^9 - n^3` -/
theorem nine_dvd_nine_minus_three (n : ℤ) : 9 ∣ n^9 - n^3 := by
  classical
  -- 因数分解を使う形に書き換え
  have F := factor n
  -- 3 で割れるかどうかで分岐
  by_cases h0 : (3 : ℤ) ∣ n
  · -- 3 ∣ n → 9 ∣ n^3、したがって差も 9 で割り切れる
    rcases h0 with ⟨k, rfl⟩
    have h3 : (9 : ℤ) ∣ (3 * k)^3 := by
      -- (3k)^3 = 27 k^3
      refine ⟨3 * k^3, by ring⟩
    have h9 : (9 : ℤ) ∣ (3 * k)^9 := by
      -- (3k)^9 も 9 の倍数（9 | (3k)^3 ⇒ 9 | (3k)^9）
      --refine ⟨(3 * k)^6, ?_⟩
      ring_nf
      have H : (3 * k) ^ 9 = ((3 * k) ^ 3) ^ 3 := by ring
      simp_all only
      omega
    -- 9 が両項を割る ⇒ 差も割る
    have : (9 : ℤ) ∣ (3*k)^9 - (3*k)^3 := by exact Int.dvd_sub h9 h3
    simpa using this
  · -- 3 ∤ n のとき：n ≡ 1 か -1 (mod 3)
    have h1 : n ≡ 1 [ZMOD 3] ∨ n ≡ (-1 : ℤ) [ZMOD 3] := by
      -- Z/3Z は {0,1,2}。0 でない元は ±1 と合同。
      have : (n : ZMod 3) ≠ 0 := by
        -- もし 0 なら 3 | n に矛盾
        intro hz
        have : (3 : ℤ) ∣ n := by
          simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hz
        exact h0 this
      -- 非零元は 1 または 2。2 は整数では -1 と同じ合同類。
      have hcases : (n : ZMod 3) = 1 ∨ (n : ZMod 3) = 2 := by
        have h : (n : ZMod 3) ≠ 0 := by
          exact this
        -- ZMod 3 の要素は 0, 1, 2 のみ
        have : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by
          decide
        -- h を使って 0 でないことを考慮
        rcases this (n : ZMod 3) with (h | h | h)
        · exfalso
          (expose_names; exact this_1 h)
        · left
          exact h
        · right
          exact h
        --fin_cases (n : ZMod 3) <;> simp [*] -- 全探索
      rcases hcases with hcases | hcases
      · left

        have : (n : ZMod 3) = 1 := by
          exact hcases
        rw [ZMod.intCast_eq_iff] at this
        obtain ⟨k, hk⟩ := this
        rw [hk]
        exact modEq_add_fac_self

      · right
        -- 2 ≡ -1 (mod 3)
        have : (2 : ZMod 3) = (-1 : ℤ) := by decide
        rw [ZMod.intCast_eq_iff] at hcases
        obtain ⟨k, hk⟩ := hcases
        rw [hk, this]
        exact modEq_add_fac_self

        --simpa [Int.cast_zmod, this] using hcases
    -- いずれの場合も `(n-1)` or `(n+1)` が 3 で割れ、かつ一方の二次因子も 3 で割れる
    have h_pair :
        (3 : ℤ) ∣ (n - 1) ∧ (3 : ℤ) ∣ (n^2 + n + 1) ∨
        (3 : ℤ) ∣ (n + 1) ∧ (3 : ℤ) ∣ (n^2 - n + 1) := by
      rcases h1 with hpos | hneg
      · -- n ≡ 1 → n-1 と n^2+n+1 が 3 で割れる
        have hL : (3 : ℤ) ∣ n - 1 := by
          -- `n ≡ 1` は `n - 1 ≡ 0`
          exact dvd_self_sub_of_emod_eq hpos

        have hQ : (3 : ℤ) ∣ n^2 + n + 1 := three_dvd_quadratic_pos n hpos
        exact Or.inl ⟨hL, hQ⟩
      · -- n ≡ -1 → n+1 と n^2-n+1 が 3 で割れる
        have hR : (3 : ℤ) ∣ n + 1 := by
          -- `n ≡ -1` は `n + 1 ≡ 0`
          have : (n + 1 : ℤ) ≡ 0 [ZMOD 3] := by
            calc
              n + 1 ≡ (-1 : ℤ) + 1 [ZMOD 3] := by
                apply Int.ModEq.add_right
                exact hneg
              _ = 0 := by norm_num
          exact Int.modEq_zero_iff_dvd.mp this

          --simpa using (hneg.add_right 1).dvd
        have hQ : (3 : ℤ) ∣ n^2 - n + 1 := three_dvd_quadratic_neg n hneg
        exact Or.inr ⟨hR, hQ⟩
    -- 3 が 2 回現れるので 9 が積を割る

    rcases h_pair with (⟨hA, hB⟩ | ⟨hC, hD⟩)
    · -- ケース1: hA: 3∣n-1, hB: 3∣n^2+n+1
      have h9 : 9 ∣ (n-1)*(n^2+n+1) := by
        have := mul_dvd_mul hA hB
        rw [mul_comm] at this
        exact this
      have : 3*3 ∣ (n-1)*(n^2+n+1) := mul_dvd_mul hA hB

      -- そして全体の式がこの積を含むので、9で割り切れる
      rw [F]
      rw [show (3 : ℤ) * 3 = 9 by norm_num] at this
      apply dvd_mul_of_dvd_left
      have H : (n - 1) * (n ^ 2 + n + 1) * (n ^ 3 * (n + 1)) = n ^ 3 * (n - 1) * (n ^ 2 + n + 1) * (n + 1) := by ring
      rw [← H]
      exact dvd_mul_of_dvd_left h9 (n ^ 3 * (n + 1))
    · -- ケース2: hC: 3∣n+1, hD: 3∣n^2-n+1
      have h9 : 9 ∣ (n + 1) * (n ^ 2 - n + 1) := by
        have : 3 * 3 ∣ (n + 1) * (n ^ 2 - n + 1) := mul_dvd_mul hC hD
        rwa [show (3 : ℤ) * 3 = 9 by norm_num] at this

      rw [F]
      have H : n ^ 3 * (n - 1) * (n ^ 2 + n + 1) * (n + 1) * (n ^ 2 - n + 1) =
          (n ^ 3 * (n - 1) * (n ^ 2 + n + 1)) * ((n + 1) * (n ^ 2 - n + 1)) := by
        ring
      rw [H]
      exact Dvd.dvd.mul_left h9 (n ^ 3 * (n - 1) * (n ^ 2 + n + 1))

----

theorem group_hom_map_inv {G G' : Type*} [Group G] [Group G']
(f : G →* G') (x : G) : f (x⁻¹) = (f x)⁻¹ :=
by
  -- `(f x)⁻¹` の一意性から、`f x * f (x⁻¹) = 1` を示せば十分です。
  -- `a * b = 1` ならば `b = a⁻¹` という定理 `eq_inv_of_mul_eq_one_right` を適用します。
  apply eq_inv_of_mul_eq_one_right
  -- ゴールは `f x * f (x⁻¹) = 1` となります。
  -- f は群準同型なので `f a * f b = f (a * b)` が成り立ちます (map_mul)。
  -- `← map_mul` で `f x * f (x⁻¹)` を `f (x * x⁻¹)` に書き換えます。
  rw [← map_mul]
  -- ゴールは `f (x * x⁻¹)` = 1 となります。
  -- 群の公理から `x * x⁻¹ = 1` です (mul_inv_self)。
  simp_all only [mul_inv_cancel, map_one]
  -- ゴールは `f 1 = 1` となります。

---

--variable {G : Type _} [CommMonoid G] [Group G] [Fintype G] [DecidableEq G]

/-- Fin p の積を  分解する標準補題 -/
lemma fin_prod_eq_mul_prod_castSucc  {G : Type _} [CommMonoid G] {p : ℕ} (hp : 1 < p) (g : Fin p → G) :
  ∏ i, g i
    =
  (∏ j : Fin (p - 1), g (Fin.cast (by omega : (p - 1) + 1 = p) (Fin.castSucc j))) *
  g (Fin.cast (by omega : (p - 1) + 1 = p) (Fin.last (p - 1))) := by
  classical
  -- まず p = (p-1)+1 に直す
  have h : (p - 1) + 1 = p := by omega
  -- Fin (p) 上の関数 g を、型を (p-1)+1 に戻した関数 F に置き換える
  let F : Fin ((p - 1) + 1) → G := fun i => g (Fin.cast h i)
  -- 既存補題：∏_{i : Fin (n+1)} F i = (∏_{j : Fin n} F j.castSucc) * F (Fin.last n)
  -- を n := p-1, F として適用し、最後に定義通りに戻すだけ

  --simp [F, h]
  let fp := (Fin.prod_univ_castSucc F)
  simp only [F] at fp
  convert fp
  exact id (Eq.symm h)
  simp_all only
  ext : 1
  simp_all only [Fin.coe_cast]
  congr
  simp_all only


    /-- Cauchy の定理 -/
theorem cauchy_theorem  {G : Type _} [CommGroup G]  [Fintype G] [DecidableEq G] {p : ℕ} (hp_prime : p.Prime) (hp_dvd : (Fintype.card G) % p = 0) :
    ∃ g : G, orderOf g = p := by
  have hp_pos : 1 < p := by
    have : 0 < p := by exact hp_prime.pos--Nat.prime_pos (by assumption)
    cases p
    · simp at this
    · simp
      simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      apply Nat.pos_of_ne_zero
      simp_all only [ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [zero_add]
      have fwd : False := prime_one_false hp_prime
      clear hp_prime
      simp_all only

  let X := { f : Fin p → G // ∏ i, f i = 1 }

  -- 同型 : (Fin (p-1) → G) ≃ X
  let α := Fin (p - 1)
  let toX : (α → G) → X := fun g =>
    let f : Fin p → G := fun i =>
      if h : i.val < p - 1 then
        g ⟨i.val, h⟩
      else
        (∏ j : α, g j)⁻¹
    ⟨f, by
      dsimp [f]
      -- Fin.prod を分解して最後の成分を取り出す
      have hp1 : 1 < p := hp_pos
      calc
        ∏ i, f i = (∏ j : Fin (p - 1), f (⟨Fin.castSucc j,by
          simp_all only [Fin.coe_castSucc]
          omega
        ⟩)) * f (⟨Fin.last (p - 1),by
          simp_all only [Fin.val_last, tsub_lt_self_iff, zero_lt_one, and_true]
          positivity
        ⟩) := by
          exact fin_prod_eq_mul_prod_castSucc hp1 f

        _ = (∏ j : α, g j) * f (⟨Fin.last (p - 1),by
          simp_all only [Fin.val_last, tsub_lt_self_iff, zero_lt_one, and_true]
          positivity
        ⟩) := by
          -- castSucc j は i.val < p-1 の場合に対応するので f (castSucc j) = g j
          simp [f]
          simp_all only [mul_inv_cancel, α]
        _ = (∏ j : α, g j) * (∏ j : α, g j)⁻¹ := by
          -- Fin.last (p - 1) の場合は else 分岐なので (∏ g)⁻¹ が返る
            have : f (⟨Fin.last (p - 1), by
              simp_all only [Fin.val_last, tsub_lt_self_iff, zero_lt_one, and_true]
              positivity
            ⟩) = (∏ j : α, g j)⁻¹ := by simp [f]
            rw [this]

        _ = 1 := by simp
    ⟩


  let ofX : X → (α → G) := fun ⟨f, hf⟩ => fun j => f (Fin.cast (by omega : (p - 1) + 1 = p) (Fin.castSucc j))
  have left_inv : ∀ g, ofX (toX g) = g := by
    intro g
    simp_all only [Fin.coe_cast, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, α, ofX, X, toX]

  have right_inv : ∀ x : X, toX (ofX x) = x := by
    intro ⟨f, hf⟩
    dsimp [toX, ofX]
    ext i
    dsimp [toX, ofX]
    by_cases h : i.val < p - 1
    · simp [h]
    · simp [h]
      have h_decomp := fin_prod_eq_mul_prod_castSucc hp_pos f
      rw [hf] at h_decomp
      have h' : (∏ j : Fin (p - 1), f (Fin.cast (by omega) (Fin.castSucc j))) * f (Fin.cast (by omega) (Fin.last (p - 1))) = 1 := by
        rw [← h_decomp]
      have : i = Fin.cast (by omega) (Fin.last (p - 1)) := by
        apply Fin.ext
        have : i.val = p - 1 := by omega
        simp [Fin.cast, Fin.last, this]
      rw [this]
      exact (eq_inv_of_mul_eq_one_right h').symm
  have e : (α → G) ≃ X := Equiv.ofBijective toX ⟨
    fun a b h => by
      have : ofX (toX a) = ofX (toX b) := congrArg ofX h
      simp [left_inv] at this
      exact this,
    fun x => ⟨ofX x, by simp [right_inv]⟩⟩
  -- build a Fintype instance for X from the equivalence, so we can talk about Fintype.card X
  haveI : Fintype X := Fintype.ofEquiv (α → G) e
  have hcard := Fintype.card_congr e
  have card_X : Fintype.card X = (Fintype.card G) ^ (p - 1) := by
    simp_all only [Fin.coe_cast, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, implies_true, Fin.castSucc_mk,
    Fin.cast_mk, dite_eq_ite, Subtype.forall, Subtype.mk.injEq, Fintype.card_pi, prod_const, Finset.card_univ,
    Fintype.card_fin, α, ofX, X, toX]

  -- p ∣ |G| より p ∣ |X|
  have cardG_mod_p : (Fintype.card G) % p = 0 := hp_dvd
  have cardX_mod_p : (Fintype.card X) % p = 0 := by
    rw [card_X]
    have hdvd : p ∣ Fintype.card G := by
      simpa using dvd_iff_mod_eq_zero.mpr cardG_mod_p
    have : p ∣ (Fintype.card G) ^ (p - 1) := by
      let dd := dvd_iff_mod_eq_zero.mpr cardG_mod_p
      by_cases hp: p = 1
      · simp at hp
        rw [hp]
        simp
      · have : p - 1 ≠ 0 := by omega
        exact dvd_pow dd  this

    exact Nat.mod_eq_zero_of_dvd this

  -- Cp = ZMod p の作用を定義 (shift)
  let Cp := ZMod p
  let actionFn : Cp → (Fin p → G) → Fin p → G := by
    refine fun k f i => f ⟨((i : ℕ) + k.val) % p, Nat.mod_lt ((i : ℕ) + k.val) (zero_lt_of_lt hp_pos)⟩

  haveI : NeZero p := ⟨by
    intro hp0
    subst hp0
    simp at hp_pos
    ⟩

  have action_preserves_product :
  ∀ (k : Cp) (f : Fin p → G), ∏ i, actionFn k f i = ∏ i, f i := by
    intro k f


    -- Fin.prod を分解して最後の成分を取り出す
    have hp1 : 1 < p := hp_pos
    calc
      ∏ i, actionFn k f i = (∏ j : Fin (p - 1), actionFn k f (⟨Fin.castSucc j,by
        simp_all only [Fin.coe_castSucc]
        omega
      ⟩)) * actionFn k f (⟨Fin.last (p - 1),by
        simp_all only [Fin.val_last, tsub_lt_self_iff, zero_lt_one, and_true]
        positivity
      ⟩) := by
        exact fin_prod_eq_mul_prod_castSucc hp1 (actionFn k f)

      _ = (∏ j : Fin (p - 1), f (⟨(j.val + k.val) % p, Nat.mod_lt _ (zero_lt_of_lt hp1)⟩)) *
          f (⟨((Fin.last (p - 1)).val + k.val) % p, Nat.mod_lt _ (zero_lt_of_lt hp1)⟩) := by
            simp [actionFn]
      _ = ∏ i, f i := by
        -- 全射性を使って和集合を入れ替える

        have : Function.Surjective (fun j : Fin p => (⟨(j.val + k.val) % p, Nat.mod_lt (j.val + k.val) (zero_lt_of_lt hp1)⟩ : Fin p)) := by
          intro y
          have hb_lt : (ZMod.val k) < p := by
          -- [NeZero p] から ZMod.val k < p
            simpa using ZMod.val_lt k

          set a : ℕ := (↑y : ℕ)
          set b : ℕ := ZMod.val k

          -- (( (a + p - b) % p + b) % p) = ((a + p - b + b) % p)
          have h1 :
            (( (a + p - b) % p + b) % p) = ((a + p - b + b) % p) := by
            -- Nat.add_mod の対称形と b % p = b（b < p）を使う
            have h := (Nat.add_mod (a + p - b) b p).symm
            have hbmod : b % p = b := Nat.mod_eq_of_lt hb_lt
            -- 左辺・右辺ともに b % p を b に置換
            -- （`simpa [hbmod] using h` と同等だが、`simpa` を避けて書く）
            -- 右向きに書き換える
            have : ((a + p - b) % p + b % p) % p = (a + p - b + b) % p := h
            -- b % p を b に置換
            exact by
              -- 左辺を書き換え
              have := congrArg (fun x => (( (a + p - b) % p + x) % p)) hbmod
              -- 右辺はそのまま
              -- これで目標と一致
              simp

          -- b ≤ a + p を示して (a + p - b) + b = a + p を得る
          have hb_le_ap : b ≤ a + p := by
            have hb_lt_ap : b < a + p := lt_of_lt_of_le hb_lt (Nat.le_add_left _ _)
            exact le_of_lt hb_lt_ap

          have h2 : (a + p - b) + b = a + p := Nat.sub_add_cancel hb_le_ap

          -- (a + p) % p = a % p （p で 1 回の加算は剰余で消える）
          have h3 : (a + p) % p = a % p := by
            -- (a + p*1) % p = a % p
            have h' := Nat.add_mul_mod_self_left a 1 p
            -- p*1 を p に書き換え
            simp

          use (⟨(y.val + p - k.val) % p, Nat.mod_lt (y.val + p - k.val) (zero_lt_of_lt hp1)⟩ : Fin p)
          apply Fin.ext
          simp
          dsimp [a,b] at h1
          dsimp [b]
          dsimp [a,b] at h2
          rw [h2]
          dsimp [a,b] at h3
          rw [h3]
          have hy : (↑y : ℕ) < p := Fin.is_lt y
          exact Nat.mod_eq_of_lt hy
        have hp0 : 0 < p := Nat.lt_trans Nat.zero_lt_one hp1

        -- 回転後の関数を一旦 g と名付ける
        let g : Fin p → G :=
          fun i => f ⟨((↑i : ℕ) + ZMod.val k) % p, Nat.mod_lt _ hp0⟩

        -- (1) Fin p の積を「castSucc 部分の積 × last の項」に分解（向きを合わせるために .symm）
        have h_split :
            (∏ j : Fin (p - 1), g (Fin.cast (by omega : (p - 1) + 1 = p) (Fin.castSucc j))) *
            g (Fin.cast (by omega : (p - 1) + 1 = p) (Fin.last (p - 1))) = ∏ i : Fin p, g i :=
          (fin_prod_eq_mul_prod_castSucc hp1 g).symm

        -- (1) と (2) を連鎖してゴールそのものに書き戻す
        simp_all only [Fin.coe_cast, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, implies_true, Fin.castSucc_mk,
          Fin.cast_mk, dite_eq_ite, Subtype.forall, Subtype.mk.injEq, Fintype.card_pi, prod_const, Finset.card_univ,
          Fintype.card_fin, Fin.val_last, α, ofX, X, toX, g]

        have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
        -- removed unused equiv between ZMod p and Fin p to avoid referencing a missing constant

        let e : ZMod p ≃ Fin p := (ZMod.finEquiv p).symm.toEquiv
        -- ZMod 側での「+ k」による自己同型
        let rotZ : ZMod p ≃ ZMod p :=
          { toFun    := fun x => x + k
            invFun   := fun x => x - k
            left_inv := by intro x; simp
            right_inv:= by intro x; simp
          }

        -- Fin 側に持ち上げた置換（これが i ↦ ((i + k) mod p) に一致）
        -- σ を簡潔に定義
        let σ : Fin p → Fin p :=
          fun i => ⟨((i : ℕ) + (ZMod.val k)) % p, Nat.mod_lt _ hp⟩

        -- これで hσ は自明
        have hσ :
            (fun i : Fin p =>
              f ⟨((i : ℕ) + (ZMod.val k)) % p, Nat.mod_lt _ (Nat.succ_le_of_lt hp)⟩)
          = (fun i => f (σ i)) := by
          -- σ の定義により、両辺は定義上等しい
          rfl

        -- 置換 `σ` による再添字で有限積は不変
        have h_perm : ∏ i : Fin p, f (σ i) = ∏ i : Fin p, f i := by
          have σ_bij : Function.Bijective σ := Function.Surjective.bijective_of_finite this
          apply Finset.prod_bij  (fun a _ => σ a)
          exact fun a ha ↦ mem_univ (σ a)
          · intro a ha b hb h
            apply σ_bij.1
            exact h
          · intro b hb
            obtain ⟨a, ha⟩ := σ_bij.2 b
            use a
            have : a ∈ Finset.univ := by exact Finset.mem_univ a
            use this
          · intro a ha
            exact rfl

        -- 仕上げ：左辺を (f ∘ σ) に書き換えてから、h_perm を適用
        have : ∏ x : Fin p, f ⟨((x : ℕ) + ZMod.val k) % p, Nat.mod_lt _ hp⟩
                = ∏ i : Fin p, f i := by
          simpa [hσ]

        -- これが欲しかったゴール
        exact this


  have action_on_X : ∀ (k : Cp) (x : X), (∏ i, actionFn k x.val i) = 1 := by
    intro k ⟨f, hf⟩
    calc
      (∏ i, actionFn k f i) = ∏ i, f i := by
        simp_all only [Fin.coe_cast, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, implies_true, Fin.castSucc_mk,
         Fin.cast_mk, dite_eq_ite, Subtype.forall, Subtype.mk.injEq, Fintype.card_pi, prod_const, Finset.card_univ,
         Fintype.card_fin, α, ofX, X, toX, Cp, actionFn]


      _ = 1 := hf
  let actionX : Cp → X → X :=
    fun k ⟨f, hf⟩ => ⟨fun i => actionFn k f i, by
      simp_all only [Fin.coe_cast, Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, implies_true, Fin.castSucc_mk,
    Fin.cast_mk, dite_eq_ite, Subtype.forall, Subtype.mk.injEq, Fintype.card_pi, prod_const, Finset.card_univ,
    Fintype.card_fin, α, ofX, X, toX, Cp, actionFn]
    ⟩

  -- Fix_X を定義し、Fix_X と {x : G | x^p = 1} は同型
  let Fix_X := {x : X // ∀ k : Cp, actionX k x = x}

  -- {x | x^p = 1} は 1 を含むので p で割れることから p 個以上の元を含む => 非自明元が存在
  have exists_nontrivial_pow_one : ∃ x : G, x ≠ 1 ∧ x ^ p = 1 := by
    let S := {x : G // x ^ p = 1}
    have one_in : (⟨1, by simp⟩ : S) ∈ (univ : Finset S) := by simp
    have cardS_pos: 0 < Fintype.card S := by
      have ex: ∃ s :S, True:= by use ⟨1, by simp⟩;
      apply Fintype.card_pos_iff.mpr
      exact Exists.nonempty ex


    have cardS_ge_p : Fintype.card S ≥ p := by
      apply Nat.le_of_dvd
      exact cardS_pos
      sorry -- 証明が大変そう。
    have : Fintype.card S > 1 := by linarith
    have : ∃ s : S, s.val ≠ 1 := by
      have : Fintype.card S > 1 := by linarith
      by_contra! h
      have : Fintype.card S = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        refine ⟨⟨1, by simp⟩, ?_⟩
        intro s
        ext
        simp [h s]
      linarith
    obtain ⟨s, hs⟩ := this
    use s.val
    constructor
    · intro h
      have : s.val = 1 := h
      contradiction
    · exact s.property

  obtain ⟨x, x_ne, x_pow⟩ := exists_nontrivial_pow_one
  -- x^p = 1 かつ x ≠ 1 => orderOf x divides p 且つ >1, 従って orderOf x = p
  have ord_dvd : orderOf x ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    exact x_pow
  have ord_gt_one : 1 < orderOf x := by
    have ord_pos : 0 < orderOf x := orderOf_pos x
    have ord_ne_one : orderOf x ≠ 1 := by
      intro h
      have : x = 1 := orderOf_eq_one_iff.mp h
      contradiction
    omega

  have ord_eq_p : orderOf x = p := by
    -- orderOf x > 1 and divides the prime p, so must equal p
    have : orderOf x ∣ p := ord_dvd
    have : orderOf x = 1 ∨ orderOf x = p := by
      exact (dvd_prime hp_prime).mp ord_dvd
    cases this
    · exfalso
      apply x_ne
      --have := congrArg (fun n => x ^ n)
      simp at this
      rename_i h'
      dsimp [orderOf] at h'
      exact orderOf_eq_one_iff.mp h'
    · (expose_names; exact h)
  use x
