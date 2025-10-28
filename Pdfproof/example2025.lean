import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sum
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
