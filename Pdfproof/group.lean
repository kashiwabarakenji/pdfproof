import Mathlib.Algebra.Group.Defs

-----------
---練習1----
-----------

-- Gを型として定義し、*という二項演算があるとします
variable {G : Type} [Mul G]

-- 単位元の一意性を示すための定理を定義します
theorem unique_identity (e e' : G) (h_e : ∀ a : G, e * a = a ∧ a * e = a)
    (h_e' : ∀ a : G, e' * a = a ∧ a * e' = a) : e = e' :=
by
  -- e'を右から掛けることにより等式を導きます
  calc
    e = e' * e := by rw [(h_e' e).1]
    _ = e' := by rw [(h_e e').2]

-----------
---練習2----
-----------

-- M をモノイドとする
variable {M : Type} [Monoid M]

-- 逆元の一意性を示す定理
theorem unique_inverse (x y z : M) (hy : x * y = 1 ∧ y * x = 1) (hz : x * z = 1 ∧ z * x = 1) : y = z :=
by
  calc
    y = y * 1 := by rw [mul_one]
    _ = y * (x * z) := by rw [hz.1]
    _ = y * x * z := by rw [mul_assoc]
    _ = 1 * z := by rw [hy.2]
    _ = z := by rw [one_mul]
