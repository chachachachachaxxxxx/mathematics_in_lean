import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

--@compare
theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with h | h
  · rw [abs_of_nonneg h]
    apply add_le_add
    repeat apply le_abs_self
  · rw [abs_of_neg h]
    rw [neg_add]
    apply add_le_add
    repeat apply neg_le_abs_self

--how to split V to prove
--@compare
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro xlty
    rcases le_or_gt 0 y with h | h
    · left
      rw [← abs_of_nonneg h]
      exact xlty
    · right
      rw [← abs_of_neg h]
      exact xlty
  intro h
  rcases le_or_gt 0 y with yle | ygt
  · rw [abs_of_nonneg yle]
    rcases h with h1 | h2
    · exact h1
    · linarith
  · rw [abs_of_neg ygt]
    rcases h with h1 | h2
    · linarith
    · exact h2

--@compare
theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro absxley
    rcases le_or_gt 0 x with h | h
    rw [abs_of_nonneg h] at absxley
    constructor
    · linarith
    · exact absxley
    rw [abs_of_neg h] at absxley
    constructor
    · linarith
    · linarith
  · rintro ⟨left, right⟩
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      exact right
    · rw [abs_of_neg h]
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

--@compare
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h2: (x - 1) * (x + 1) = 0 := by
    ring_nf
    rw [h]
    ring
  have h3: x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

--@compare
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h': P
    right; apply h h'
    left; exact h'
  · rintro h h'
    cases h
    case mpr.inl h1 =>
      exact False.elim (h1 h')
    case mpr.inr h1 =>
      exact h1
