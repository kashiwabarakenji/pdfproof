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
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
--import Mathlib.Data.Int.Modeq
import Mathlib.Tactic
import LeanCopilot
--import Mathlib
open Finset
open Int
open scoped BigOperators
--import Mathlib.Data.Finset.Range
--import Mathlib.Algebra.BigOperators.FinSupp.Basic

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
