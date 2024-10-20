import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic
import GarsideMonoid.Basic

/-
Example 2.2

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
  -- f g = h means ∀ k, f(k) + g(k) = h(k) --
  mul f g := fun k ↦ f k + g k

theorem mul_apply (f g : NatSequence n) (k : Fin n) : (f * g) k = f k + g k := by rfl

instance : Semigroup (NatSequence n) where
  mul_assoc f g h := by
    ext k
    repeat rw [mul_apply]
    rw [add_assoc]

instance : One (NatSequence n) where
  one := fun _ ↦ 0

theorem one_apply (k : Fin n) : (1 : NatSequence n) k = 0 := by rfl

-- Then ℕⁿ is a monoid --
instance : Monoid (NatSequence n) where
  one_mul f := by ext k; rw [mul_apply, one_apply]; simp
  mul_one f := by ext k; rw [mul_apply, one_apply]; simp

-- For f, g in ℕⁿ, define f ≼ g to mean ∀ k, f(k) ≤ g(k) --
theorem left_dvd_iff (f g : NatSequence n) : f ≼ₗ g ↔ ∀ k, f k ≤ g k := by
  constructor
  . intro ⟨d, hd⟩ k
    have := congrFun hd k
    rw [mul_apply] at this
    exact Nat.le.intro this
  . intro h
    use (fun k ↦ g k - f k); ext k
    rw [mul_apply]
    exact Nat.add_sub_of_le (h k)

theorem right_dvd_iff (f g : NatSequence n) : f ≼ᵣ g ↔ ∀ k, f k ≤ g k := by
  constructor
  . intro ⟨d, hd⟩ k
    have := congrFun hd k
    rw [mul_apply, add_comm] at this
    exact Nat.le.intro this
  . intro h
    use (fun k ↦ g k - f k); ext k
    rw [mul_apply]
    exact Nat.sub_add_cancel (h k)

def gcd (f g : NatSequence n) := fun k ↦ min (f k) (g k)

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

-- ℕⁿ is cancellative --
instance : CancelMonoid (NatSequence n) where
  mul_left_cancel f g h := by
    intro heq; ext k
    have := congrFun heq k
    repeat rw [mul_apply] at this
    exact Nat.add_left_cancel this
  mul_right_cancel f g h := by
    intro heq; ext k
    have := congrFun heq k
    repeat rw [mul_apply] at this
    exact Nat.add_right_cancel this

/- We can define λ(g) to be the common length of all Aₙ-words
representing an element g of ℕⁿ -/
def lambda (g : NatSequence n) := ∑ k, g k

theorem lambda_ord (f g : NatSequence n) : lambda (f * g) ≥ lambda f + lambda g := by
  unfold lambda
  have : ∀ k ∈ Finset.univ, (f * g) k = f k + g k := by exact fun k _ ↦ rfl
  rw [Finset.sum_congr (by rfl) this]
  apply le_of_eq
  rw [Finset.sum_add_distrib]

theorem lambda_nonzero (g : NatSequence n) : g ≠ 1 → lambda g ≠ 0 := by
  contrapose!; intro h
  unfold lambda at h
  -- simp is pretty smart sometimes! --
  simp at h
  ext k; rw [one_apply]; exact h k

-- Aₙ generate ℕⁿ --
def A_map (k : Fin n) : NatSequence n := fun j ↦ if j = k then 1 else 0

lemma A_inj : Function.Injective (@A_map n) := by
  intro k k' h
  unfold A_map at h
  have := congrFun h k
  simp at this
  by_contra h'
  rw [if_neg h'] at this
  linarith

def A_emb : Function.Embedding (Fin n) (NatSequence n):= ⟨A_map, A_inj⟩

def A := (Finset.map (@A_emb n) Finset.univ).toSet

theorem lambda_ind (motive: NatSequence n → Prop) (h₁ : motive 1)
    (h₂ : (l : ℕ) → (∀ x, lambda x ≤ l → motive x) → (y : NatSequence n) → lambda y = l.succ → motive y)
    (f : NatSequence n) : motive f := by sorry

theorem A_gen (n : ℕ) : Submonoid.closure (@A n) = ⊤ := by
  apply (Submonoid.eq_top_iff' (Submonoid.closure A)).mpr
  intro x; apply Submonoid.mem_sInf.mpr
  intro M hM; simp at hM
  induction x using lambda_ind
  next => exact Submonoid.one_mem M
  next l hl g hg =>
    by_cases h : g = 1
    . rw [h]; exact Submonoid.one_mem M
    . -- g ≠ 1, thus there is non-zero element --
      obtain ⟨k, hk⟩ : ∃ k, g k ≠ 0 := by
        by_contra h'
        push_neg at h'
        have : g = 1 := by ext k; rw [one_apply]; exact h' k
        contradiction
      rw [← Nat.one_le_iff_ne_zero] at hk
      -- then we can construct strict divisor g' --
      let g' : NatSequence n := fun j ↦ if k = j then g j - 1 else g j
      have hg'k : g' k = g k - 1 := by unfold g'; simp
      have hg'neqk : ∀ j ∈ Finset.filter (fun x ↦ ¬k = x) Finset.univ, g' j = g j := by
        intro j h; unfold g'
        simp at h; rw [if_neg h]
      have hmul : g = g' * A_map k := by
        ext j
        rw [mul_apply]
        unfold A_map
        by_cases hj : j = k
        . rw [if_pos hj, hj, hg'k]
          exact (Nat.sub_eq_iff_eq_add hk).mp rfl
        . unfold g'; rw [if_neg hj]
          rw [if_neg fun a ↦ hj (id (Eq.symm a))]
          simp
      -- g' has maximal λ --
      have hsum (x : NatSequence n) : x.lambda = x k + (Finset.filter (fun x ↦ ¬k = x) Finset.univ).sum x := by
        unfold lambda
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (Eq k)]
        rw [Finset.filter_eq]
        simp [hg'k]
      have : g'.lambda = l := by
        rw [hsum g', hg'k]
        rw [Finset.sum_congr (by rfl) hg'neqk]
        rw [hsum g] at hg
        rw [← Nat.sub_add_comm hk, hg]
        rfl
      -- Aₙ is contained in submonoid by definition --
      have ha : A_map k ∈ M := by
        unfold A A_emb at hM
        simp at hM
        have : A_map k ∈ Set.range fun j ↦ A_map j := by exact Set.mem_range_self k
        exact hM this
      specialize hl g' (by linarith); rw [hmul]
      exact Submonoid.mul_mem M hl ha

-- Define Δₙ ∈ ℕⁿ as Δₙ(k) = 1 for k=1,…,n. --
def Δ : NatSequence n := fun _ ↦ 1

-- Its divisors include Aₙ and generate ℕⁿ --
def div_Δ : Set (NatSequence n) := {g | ∀ k, g k ≤ 1}

theorem Δ_gen_include_A (n : ℕ) : @A n ⊆ div_Δ := by
  intro g hA; unfold A A_emb at hA
  simp at hA; obtain ⟨k, hk⟩ := hA
  unfold div_Δ; rw [← hk]; simp
  unfold A_map; intro j
  by_cases h : j = k
  . rw [if_pos h]
  . rw [if_neg h]
    norm_num

theorem Δ_gen : Submonoid.closure (@div_Δ n) = ⊤ := by
  have h := Δ_gen_include_A n
  apply (Submonoid.eq_top_iff' (Submonoid.closure div_Δ)).mpr
  intro x; unfold Submonoid.closure; rw [Submonoid.mem_sInf]; intro M hM
  have := (Submonoid.eq_top_iff' (Submonoid.closure A)).mp (A_gen n)
  specialize this x; unfold Submonoid.closure at this
  rw [Submonoid.mem_sInf] at this; specialize this M
  simp at hM; simp at this; apply this; exact fun _ hx ↦ hM (h hx)

-- The family Div(Δₙ) is finite, since it has 2ⁿ elements --

end NatSequence
