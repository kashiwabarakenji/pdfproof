import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.ModEq
import Mathlib
open Finset
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
