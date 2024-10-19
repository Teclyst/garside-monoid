import Mathlib.Algebra.Group.Defs

/-
Recall that a monoid M is left-cancellative (resp. right-cancellative)
if fg = fg' (resp. gf = g'f) implies g = g', and cancellative if
it is both left- and right-cancellative.
-/

#check LeftCancelMonoid
#check RightCancelMonoid
#check CancelMonoid

#check Dvd

/--
We say that f is a left-divisor of g, or, equivalently,
that g is a right-multiple of f, written f ≼ g,
if there exists g' in M satisfying fg' = g
-/
class LeftDvd (α : Type*) where
  /-- Left-divisibility. `a ≼ b` (typed as `\preceq`) means that there is some `c` such that `b = a * c`. -/
  left_dvd : α → α → Prop

@[inherit_doc] infix:50  " ≼ₗ " => LeftDvd.left_dvd

-- Similar to how Dvd instance is defined Mathlib.Algebra.Divisibility.Basic --
instance (α : Type*) [Semigroup α] : LeftDvd α where
  left_dvd f g := ∃ g', f * g' = g

/--
For g'f = g, we symmetrically say that f is a right-divisor of g,
or equivalently, that g is a left-multiple of f.
-/
class RightDvd (α : Type*) where
  /-- Right-divisibility of `b` by `a`. Means that there is some `c` such that `b = c * a`. -/
  right_dvd: α → α → Prop

@[inherit_doc] infix:50  " ≼ᵣ " => LeftDvd.left_dvd

instance (α : Type*) [Semigroup α] : RightDvd α where
  right_dvd f g := ∃ g', g' * f = g

-- -- Similar to how GCDMonoid is defined at Mathlib.Algebra.GCDMonoid.Basic --
class LeftRightGCDMonoid (M : Type*) extends Monoid M, LeftDvd M, RightDvd M where
  -- definition taken from http://www-sop.inria.fr/cafe/Manuel.Bronstein/sumit/berninadoc/node26.html --
  left_gcd : M → M → M
  left_gcd_dvd_left : ∀ f g, (left_gcd f g) ≼ₗ f
  left_gcd_dvd_right : ∀ f g, (left_gcd f g) ≼ₗ g
  left_gcd_dvd : ∀ f g h, f ≼ₗ g → f ≼ₗ h → f ≼ₗ (left_gcd f g)

  right_gcd : M → M → M
  right_gcd_dvd_left : ∀ f g, (right_gcd f g) ≼ᵣ f
  right_gcd_dvd_right : ∀ f g, (right_gcd f g) ≼ᵣ g
  right_gcd_dvd : ∀ f g h, f ≼ᵣ g → f ≼ᵣ h → f ≼ᵣ (left_gcd f g)
  -- TODO : consolidate left/right-lcm definition --

/-
Definition 2.1. A Garside monoid is a pair (M, Δ), where
M is a cancellative monoid satisfying the following conditions:
-/
class GarsideMonoid (M : Type*) extends CancelMonoid M where
  -- (i) there exists λ : M → ℕ satisfying, for all f, g, --
  lambda : α → ℕ
  -- λ(fg) ≥ λ(f) + λ(g) --
  lambda_ord : ∀ f g : M, lambda (f * g) ≥ lambda f + lambda g
  -- g ≠ 1 ⇒ λ(g) ≠ 0 --
  lambda_nonzero : ∀ g : M, g ≠ 1 → lambda g ≠ 0

  -- (ii) Any two elements of M admit left- and right- lcms and gcds --


  -- Δ is a Garside element of M --
  Δ : M
  -- meaning that the left- and right- divisors of Δ coincide --
