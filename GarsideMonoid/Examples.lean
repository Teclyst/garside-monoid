import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import GarsideMonoid.Basic

/-
Example 2.1

Consider the free abelian monoid (ℕ, +)ⁿ with n ≥ 1,
simply denoted by ℕⁿ. We shall see the elements of ℕⁿ
as sequences of nonnegative integers indexed by {1,…,n},
thus writing g(k) for the k-th entry of an element g.
-/

def NatSequence (n : ℕ) := Fin n → ℕ

variable {n : ℕ}

namespace NatSequence

@[ext]
theorem ext (f g : NatSequence n) (h : ∀ k, f k = g k) : f = g := funext h

instance : Mul (NatSequence n) where
  -- fg = h means ∀ k, f(k) + g(k) = h(k) --
  mul f g := fun k => f k + g k

theorem mul_apply (f g : NatSequence n) (k : Fin n) : (f * g) k = f k + g k := by rfl

instance : Semigroup (NatSequence n) where
  mul_assoc f g h := by
    ext k
    repeat rw [mul_apply]
    rw [add_assoc]

instance : One (NatSequence n) where
  one := fun _ => 0

theorem one_apply (k : Fin n) : (1 : NatSequence n) k = 0 := by rfl

instance : Monoid (NatSequence n) where
  one_mul f := by ext k; rw [mul_apply, one_apply]; simp
  mul_one f := by ext k; rw [mul_apply, one_apply]; simp

theorem left_dvd_iff (f g : NatSequence n) : f ≼ₗ g ↔ ∀ k, f k ≤ g k := by
  constructor
  . intro ⟨d, hd⟩ k
    have := congrFun hd k
    rw [mul_apply] at this
    exact Nat.le.intro this
  . intro h
    use (fun k => g k - f k); ext k
    rw [mul_apply]
    exact Nat.add_sub_of_le (h k)

theorem right_dvd_iff (f g : NatSequence n) : f ≼ᵣ g ↔ ∀ k, f k ≤ g k := by
  constructor
  . intro ⟨d, hd⟩ k
    have := congrFun hd k
    rw [mul_apply, add_comm] at this
    exact Nat.le.intro this
  . intro h
    use (fun k => g k - f k); ext k
    rw [mul_apply]
    exact Nat.sub_add_cancel (h k)

def gcd (f g : NatSequence n) := fun k => min (f k) (g k)

theorem gcd_apply (f g : NatSequence n) (k : Fin n) : f.gcd g k = min (f k) (g k) := by rfl

theorem gcd_dvd_left (f g : NatSequence n) (k : Fin n) : f.gcd g k ≤ f k := by
  rw [gcd_apply]; apply Nat.min_le_left

theorem gcd_dvd_right (f g : NatSequence n) (k : Fin n) : f.gcd g k ≤ g k := by
  rw [gcd_apply]; apply Nat.min_le_right

theorem gcd_dvd (f g h : NatSequence n) (fleg : ∀ k, f k ≤ g k) (fleh : ∀ k, f k ≤ h k) :
    ∀ k, f k ≤ g.gcd h k := by
  intro k; rw [gcd_apply]; exact Nat.le_min_of_le_of_le (fleg k) (fleh k)

instance : LeftRightGCDMonoid (NatSequence n) where
  left_gcd := gcd
  left_gcd_dvd_left f g := by
    rw [left_dvd_iff]; apply gcd_dvd_left
  left_gcd_dvd_right f g := by
    rw [left_dvd_iff]; apply gcd_dvd_right
  left_gcd_dvd f g h := by
    repeat rw [left_dvd_iff]
    apply gcd_dvd

  right_gcd := gcd
  right_gcd_dvd_left f g:= by
    rw [right_dvd_iff]; apply gcd_dvd_left
  right_gcd_dvd_right f g := by
    rw [right_dvd_iff]; apply gcd_dvd_right
  right_gcd_dvd f g h := by
    repeat rw [right_dvd_iff]
    apply gcd_dvd

end NatSequence
