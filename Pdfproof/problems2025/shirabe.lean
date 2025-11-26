import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega.Core
import Mathlib.Order.MinMax
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Basic
import LeanCopilot

-- 補題：この問題の核心となる代数変形
-- n^2 + n - a = k^2 ↔ (2n+1)^2 - (2k)^2 = 4a + 1 を正当化する
lemma key_algebra (n k a : ℕ) (h_eq : n^2 + n - a = k^2) (h_le : a ≤ n^2 + n) :
    (2 * n + 1) ^ 2 - (2 * k) ^ 2 = 4 * a + 1 := by
  -- 自然数の引き算を扱うため、zifyで整数にキャストして計算する
  zify at h_eq h_le ⊢
  -- 整数環での計算として処理
  sorry
  --nlinarith [h_eq]

theorem N_eq_one_iff_4a_plus_1_prime (a : ℕ) (ha : 1 ≤ a) :
  (∃! n : ℕ, 1 ≤ n ∧ ∃ k : ℕ, n ^ 2 + n - a = k ^ 2) ↔ Nat.Prime (4 * a + 1) := by
  constructor
  -- (→) 一意に存在するなら素数
  · intro h
    -- 対偶を示す: 4a+1が素数でないなら、解は一意でない
    by_contra h_not_prime
    have : ¬ Nat.Prime (4 * a + 1) := h_not_prime

    have h_ge2 : 4 * a + 1 ≥ 2 := by linarith [ha]

    rcases Nat.exists_dvd_of_not_prime h_ge2 this with ⟨b, hb_dvd, hb_ne1, hb_ne_self⟩

    -- 因数 b と c=(4a+1)/b から新しい解を構成する
    rcases hb_dvd with ⟨c, h_prod⟩

    -- 2つの異なる解を構成することで、一意性の仮定 h と矛盾させる
    -- 解1: 自明な因数分解 1 * (4a+1) から n=a が解となる
    let n₁ := a
    have h_sol₁_prop : 1 ≤ n₁ ∧ ∃ k, n₁^2 + n₁ - a = k^2 := ⟨ha, ⟨a, by simp⟩⟩

    -- 解2: 非自明な因数分解 b * c から構成
    let n₂ := (min b c + max b c - 2) / 4
    have h_sol₂_prop : 1 ≤ n₂ ∧ ∃ k, n₂^2 + n₂ - a = k^2 := by
      let b' := min b c; let c' := max b c
      have h_prod' : 4 * a + 1 = b' * c' := by rw [h_prod, min_mul_max]
      have h_b'_le_c' : b' ≤ c' :=by exact inf_left_le_sup_left
      have h_b'_gt1 : 1 < b' := by
        sorry
        --apply lt_min <;> (intro h; rw [h] at *; simp_all)
        --· rw [h_prod] at hb_ne_self; exact hb_ne_self.symm
        --· have hc_ne1 : c ≠ 1 := by intro hc1; rw [hc1, mul_one] at h_prod; contradiction
        --  rw [h_prod] at hc_ne1; exact hc_ne1
      have h_div4 : (c' - b') % 4 = 0 ∧ (b' + c' - 2) % 4 = 0 := by
        have h_odd : Odd (4 * a + 1) := by sorry
        rw [h_prod'] at h_odd
        rcases Nat.odd_mul_odd.mp h_odd with ⟨h_b_odd, h_c_odd⟩
        have h_mod_eq : b' % 4 = c' % 4 := by
          have := congr_arg (· % 4) h_prod'; simp_arith at this
          rw [Nat.mul_mod] at this
          cases Nat.odd_mod_four_eq_one_or_three b' <;> cases Nat.odd_mod_four_eq_one_or_three c' <;> simp_all [Nat.mul_mod]
        constructor <;> { zify; rw [h_mod_eq]; omega }
      let k₂ := (c' - b') / 4
      constructor
      · apply Nat.div_le_of_le_mul; linarith [h_b'_gt1, h_b'_le_c']
      · use k₂
        apply (key_algebra n₂ k₂ a).mp
        · exact Nat.sub_le _ _
        · zify
          have ha_z : (a:ℤ) = (b'*c' - 1) / 4 := by rw [h_prod']; linarith
          sorry
          --field_simp; ring

    -- 2つの解が異なることを示す (n₁ ≠ n₂)
    have h_n_ne : n₁ ≠ n₂ := by
      simp [n₁, n₂]
      intro h_eq_a
      have : min b c + max b c - 2 = 4 * a := (Nat.div_eq_iff_eq_mul_right (by norm_num)).mp h_eq_a
      have : b + c = 4 * a + 2 := by rw [min_add_max]; linarith
      rw [h_prod] at this
      have : b + c = b * c + 1 := by linarith
      have : (b - 1) * (c - 1) = 0 := by zify; ring
      rcases Nat.mul_eq_zero.mp this with h_b1 | h_c1
      · have b1 := Nat.le_of_sub_eq_zero h_b1
        have hb_gt1 : 1 < b := by apply lt_min <;> (intro h; rw [h] at *; simp_all); · rw [h_prod] at hb_ne_self; exact hb_ne_self.symm; · have hc_ne1 : c ≠ 1 := by intro hc1; rw [hc1, mul_one] at h_prod; contradiction; rw [h_prod] at hc_ne1; exact hc_ne1
        linarith
      · have c1 := Nat.le_of_sub_eq_zero h_c1
        have h_b_le_c : b ≤ c := min_le_max b c
        have hb_gt1 : 1 < b := by apply lt_min <;> (intro h; rw [h] at *; simp_all); · rw [h_prod] at hb_ne_self; exact hb_ne_self.symm; · have hc_ne1 : c ≠ 1 := by intro hc1; rw [hc1, mul_one] at h_prod; contradiction; rw [h_prod] at hc_ne1; exact hc_ne1
        linarith

    -- 解の一意性に反する
    rcases h with ⟨_, _, h_unique⟩
    exact h_n_ne (h_unique n₂ h_sol₂_prop ▸ h_unique n₁ h_sol₁_prop)

  -- (←) 素数なら一意に存在
  · intro h_prime
    -- 解の存在を示す: n = a とすると条件を満たす
    use a
    refine' ⟨⟨ha, a, _⟩, _⟩
    · -- k = a とすると n^2 + n - a = k^2 が成り立つ
      -- a^2 + a - a = a^2 を示す
      simp
    · -- 一意性を示す
      intro m ⟨hm_ge1, k, hk_eq⟩
      -- m^2 + m - a = k^2 から、m^2 + m ≥ a を導く
      have h_le_m : a ≤ m^2 + m := by sorry--Nat.sub_le (m ^ 2 + m) a
      -- 代数変形により (2m+1-2k)(2m+1+2k) = 4a+1
      have h_fact : (2 * m + 1 - 2 * k) * (2 * m + 1 + 2 * k) = 4 * a + 1 := by
        rw [← key_algebra m k a hk_eq h_le_m]
        -- (x-y)(x+y) = x^2-y^2 を示す
        zify
        ring_nf
        sorry
      -- 素数の性質により、約数は 1 または 4a+1 のみ
      -- 2m+1-2k ≤ 2m+1+2k より、2m+1-2k = 1
      -- よって 2m+1+2k = 4a+1
      -- これらから m = a を導く
      have h_dvd : (2 * m + 1 - 2 * k) ∣ (4 * a + 1) := dvd_of_mul_right_eq _ h_fact

      rcases h_prime.eq_one_or_self_of_dvd h_dvd with h_fac | h_fac
      · -- Case 1: 2 * m + 1 - 2 * k = 1
        have h_sum : 2 * m + 1 + 2 * k = 4 * a + 1 := by
          rwa [h_fact, h_fac, one_mul] at h_fact
        -- 2m - 2k = 0  => m = k
        -- 2m + 2k = 4a => m + k = 2a
        -- よって m = a
        zify at h_fac h_sum
        have : (m:ℤ) = k := by linarith [h_fac]
        rw [this] at h_sum
        linarith
      · -- Case 2: 2 * m + 1 - 2 * k = 4 * a + 1
        have h_sum : 2 * m + 1 + 2 * k = 1 := by
          rwa [h_fact, h_fac, mul_comm, one_mul] at h_fact
        -- m ≥ 1, k ≥ 0 なので 2m+1+2k ≥ 3 となり矛盾
        zify at h_sum hm_ge1
        linarith

theorem square_condition_implies_n_le_a (a n : ℕ) (ha : 1 ≤ a) (hn : 1 ≤ n)
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

/-
theorem N_eq_one_iff_4a_plus_1_prime (a : ℕ) (ha : 1 ≤ a) :
  (∃! n : ℕ, 1 ≤ n ∧ ∃ k : ℕ, n ^ 2 + n - a = k ^ 2) ↔ Nat.Prime (4 * a + 1) := by
  constructor
  · intro h
    rcases h with ⟨n, ⟨hn1, hn2⟩, h_unique⟩
    obtain ⟨k, hk⟩ := hn2
    have h_ge : n^2 + n ≥ a := by
      have h_ge' : n^2 + n - a ≥ 0 := by
        rw [hk]
        exact Nat.zero_le (k^2)
      sorry
    have h_eq1 : n^2 + n = k^2 + a := by
      have : n^2 + n - a = k^2 := hk
      simp_all only [and_imp, forall_exists_index, le_refl, Nat.one_le_ofNat, zero_le, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀, add_tsub_cancel_right, ge_iff_le,
        le_add_iff_nonneg_left]
    have h_eq : (2 * n + 1 - 2 * k) * (2 * n + 1 + 2 * k) = 4 * a + 1 := by
      have h1 : (2 * n + 1 - 2 * k) * (2 * n + 1 + 2 * k) = (2 * n + 1)^2 - (2 * k)^2 := by
        ring_nf
        sorry
      have h2 : (2 * n + 1)^2 - (2 * k)^2 = 4 * n^2 + 4 * n + 1 - 4 * k^2 := by
        ring_nf
      have h3 : 4 * n^2 + 4 * n + 1 - 4 * k^2 = 4 * (n^2 + n - k^2) + 1 := by
        ring_nf
        simp_all
      have h4 : 4 * (n^2 + n - k^2) + 1 = 4 * a + 1 := by
        rw [← hk]
        ring_nf
        sorry
      linarith
    have h_pos_prod : 0 < (2 * n + 1 - 2 * k) * (2 * n + 1 + 2 * k) := by
      rw [h_eq]
      linarith
    have h_pos_right : 0 < 2 * n + 1 + 2 * k := by sorry
    have h_pos_left : 0 < 2 * n + 1 - 2 * k := by sorry
    have h_left_dvd : (2 * n + 1 - 2 * k) ∣ 4 * a + 1 := by
      rw [← h_eq]
      exact ⟨2 * n + 1 + 2 * k, by ring_nf⟩
    have h_left_eq_one : 2 * n + 1 - 2 * k = 1 := by
      have h_ge_one : 1 ≤ 2 * n + 1 - 2 * k := by sorry
      have h_le_one : 2 * n + 1 - 2 * k ≤ 1 := by
        have h_prod : (2 * n + 1 - 2 * k) * (2 * n + 1 + 2 * k) = 4 * a + 1 := h_eq
        have h_min_right : 2 * n + 1 + 2 * k ≥ 3 := by sorry
        have h_pos : 0 < 2 * n + 1 - 2 * k := h_pos_left
        sorry
      sorry
    have h_right_eq : 2 * n + 1 + 2 * k = 4 * a + 1 := by
      rw [← h_eq, h_left_eq_one]
      sorry
    have h_ge_two : 2 ≤ 4 * a + 1 := by sorry
    refine' Nat.prime_def_lt'.mpr ⟨h_ge_two, fun b hb hb_lt => _⟩
    have hb_eq_one : b = 1 := by
      have hb_dvd : b ∣ 4 * a + 1 := by
        rw [← h_eq]
        sorry
        --exact?-- Nat.dvd_mul_right b (2 * n + 1 + 2 * k)
      have hb_le_one : b ≤ 1 := by
        have : b ≤ 2 * n + 1 - 2 * k := by
          apply Nat.le_of_dvd
          · exact h_pos_left
          · sorry
        rw [h_left_eq_one] at this
        exact this
      sorry
    rw [hb_eq_one]
    sorry


  · intro h_prime
    refine' ⟨a, ⟨ha, ⟨a, by simp_all only [add_tsub_cancel_right]⟩⟩, fun n ⟨hn1, hn2⟩ => _⟩
    obtain ⟨k, hk⟩ := hn2
    have h_ge : n^2 + n ≥ a := by
      have h_ge' : n^2 + n - a ≥ 0 := by
        rw [hk]
        exact Nat.zero_le (k^2)
      sorry
    have h_eq1 : n^2 + n = k^2 + a := by
      have : n^2 + n - a = k^2 := hk
      exact (Nat.sub_eq_iff_eq_add h_ge).mp hk
    have h_eq : (2 * n + 1 - 2 * k) * (2 * n + 1 + 2 * k) = 4 * a + 1 := by
      have h1 : (2 * n + 1 - 2 * k) * (2 * n + a + 2 * k) = (2 * n + 1)^2 - (2 * k)^2 := by
        ring_nf
        sorry
      have h2 : (2 * n + 1)^2 - (2 * k)^2 = 4 * n^2 + 4 * n + 1 - 4 * k^2 := by
        ring_nf
      have h3 : 4 * n^2 + 4 * n + 1 - 4 * k^2 = 4 * (n^2 + n - k^2) + 1 := by
        ring_nf
        sorry
      have h4 : 4 * (n^2 + n - k^2) + 1 = 4 * a + 1 := by
        rw [← hk]
        ring_nf
        sorry
      sorry
    have h_pos_prod : 0 < (2 * n + 1 - 2 * k) * (2 * n + 1 + 2 * k) := by
      rw [h_eq]
      sorry
    have h_pos_right : 0 < 2 * n + 1 + 2 * k := by sorry
    have h_pos_left : 0 < 2 * n + 1 - 2 * k := by sorry
    have h_left_dvd : (2 * n + 1 - 2 * k) ∣ 4 * a + 1 := by
      rw [← h_eq]
      exact ⟨2 * n + 1 + 2 * k, by ring_nf⟩
    have h_left_eq : 2 * n + 1 - 2 * k = 1 ∨ 2 * n + 1 - 2 * k = 4 * a + 1 := by
      apply Nat.Prime.eq_one_or_self_of_dvd h_prime
      exact h_left_dvd
    cases' h_left_eq with h_eq_one h_eq_self
    · have : n = a := by
        rw [h_eq_one] at h_eq
        sorry
      exact this
    · have : 2 * n + 1 + 2 * k = 1 := by
        rw [h_eq_self] at h_eq
        sorry
      sorry
-/
