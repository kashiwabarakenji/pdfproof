import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import LeanCopilot

open Nat

-- 1. 準備: 2進付値の定義
def v2 (n : ℕ) : ℕ := n.factorization 2

-- 2. 集合の定義
-- S = {1, 2, ..., 40}
def S : Finset ℕ := Finset.Icc 1 40

-- 3. グループ分けの定義
-- Ak = { n ∈ S | v2(n) = k }
-- つまり、「2でちょうど k 回割れる数」の集合
def Groups (k : ℕ) : Finset ℕ := S.filter (fun n => v2 n = k)

-- ここで「手計算のロジック」を定理として記述します。
theorem solve_by_logic :
  -- 全体のペア数 (40 × 40) から
  (S.card * S.card) -
  -- 条件を満たさないペア（同じグループ同士のペア）の数を引く
  ( (Groups 0).card ^ 2 + -- 奇数同士
    (Groups 1).card ^ 2 + -- 2×奇数 同士
    (Groups 2).card ^ 2 + -- 4×奇数 同士
    (Groups 3).card ^ 2 + -- 8×奇数 同士
    (Groups 4).card ^ 2 + -- 16×奇数 同士
    (Groups 5).card ^ 2    -- 32×奇数 同士
  ) = 1064 := by

  -- 【証明パート】
  -- コンピュータにブラックボックスで計算させるのではなく、
  -- 人間が手計算で確認した「各グループの個数」と一致することをステップごとに確認します。

  -- まず、全体の数は 40 である
  have h_total : S.card = 40 := by rfl

  -- グループ0 (奇数) は 20個 {1, 3, ..., 39}
  have h0 : (Groups 0).card = 20 := by
    dsimp [Groups, S]
    dsimp [S] at h_total
    dsimp [Finset.Icc]
    simp only [Finset.card_filter]
    simp
    dsimp [Finset.Icc] at h_total
    native_decide

  -- グループ1 (2の倍数かつ4でない) は 10個 {2, 6, ..., 38}
  have h1 : (Groups 1).card = 10 := by native_decide

  -- グループ2 (4の倍数かつ8でない) は 5個 {4, 12, ..., 36}
  have h2 : (Groups 2).card = 5  := by native_decide

  -- グループ3 (8の倍数かつ16でない) は 3個 {8, 24, 40}
  have h3 : (Groups 3).card = 3  := by native_decide

  -- グループ4 (16の倍数かつ32でない) は 1個 {16}
  have h4 : (Groups 4).card = 1  := by native_decide

  -- グループ5 (32の倍数) は 1個 {32}
  have h5 : (Groups 5).card = 1  := by native_decide

  -- 最後に、これらの値を式に代入して計算が合うか確認
  -- 40^2 - (20^2 + 10^2 + 5^2 + 3^2 + 1^2 + 1^2)
  -- = 1600 - (400 + 100 + 25 + 9 + 1 + 1)
  -- = 1600 - 536
  -- = 1064
  rw [h_total, h0, h1, h2, h3, h4, h5]
  -- 代入後の数値計算を実行
  norm_num

-- 証明完了 (Q.E.D.)
