import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite

/-
Recall that a monoid M is left-cancellative (resp. right-cancellative)
if f g = f g' (resp. g f = g' f) implies g = g', and cancellative if
it is both left- and right-cancellative.
-/

/--
We say that f is a left-divisor of g, or, equivalently,
that g is a right-multiple of f, written f ≼ g,
if there exists g' in M satisfying f g' = g
-/
class LeftDvd (α : Type*) where
  /-- Left-divisibility. `a ≼ b` (typed as `\preceq`) means that there is some `c` such that `b = a * c`. -/
  left_dvd : α → α → Prop

@[inherit_doc] infix:50  " ≼ₗ " => LeftDvd.left_dvd

-- Similar to how Dvd instance is defined Mathlib.Algebra.Divisibility.Basic --
instance (α : Type*) [Semigroup α] : LeftDvd α where
  left_dvd f g := ∃ g', f * g' = g

/--
For g' f = g, we symmetrically say that f is a right-divisor of g,
or equivalently, that g is a left-multiple of f.
-/
class RightDvd (α : Type*) where
  /-- Right-divisibility of `b` by `a`. Means that there is some `c` such that `b = c * a`. -/
  right_dvd: α → α → Prop

@[inherit_doc] infix:50  " ≼ᵣ " => RightDvd.right_dvd

instance (α : Type*) [Semigroup α] : RightDvd α where
  right_dvd f g := ∃ g', g' * f = g

-- -- Similar to how GCDMonoid is defined at Mathlib.Algebra.GCDMonoid.Basic --
class LeftRightGCDMonoid (M : Type*) extends Monoid M where
  -- definition taken from http://www-sop.inria.fr/cafe/Manuel.Bronstein/sumit/berninadoc/node26.html --
  left_gcd : M → M → M
  left_gcd_dvd_left : ∀ f g, (left_gcd f g) ≼ₗ f
  left_gcd_dvd_right : ∀ f g, (left_gcd f g) ≼ₗ g
  left_gcd_dvd : ∀ f g h, f ≼ₗ g → f ≼ₗ h → f ≼ₗ (left_gcd g h)

  right_gcd : M → M → M
  right_gcd_dvd_left : ∀ f g, (right_gcd f g) ≼ᵣ f
  right_gcd_dvd_right : ∀ f g, (right_gcd f g) ≼ᵣ g
  right_gcd_dvd : ∀ f g h, f ≼ᵣ g → f ≼ᵣ h → f ≼ᵣ (left_gcd g h)
  -- TODO : consolidate left/right-lcm definition --

/-
Definition 2.1. A Garside monoid is a pair (M, Δ), where
M is a cancellative monoid satisfying the following conditions:
-/
class GarsideMonoid (M : Type*) extends CancelMonoid M, LeftRightGCDMonoid M where
  -- (i) there exists λ : M → ℕ satisfying, for all f, g, --
  lambda : M → ℕ
  -- λ(f g) ≥ λ(f) + λ(g) --
  lambda_ord : ∀ f g : M, lambda (f * g) ≥ lambda f + lambda g
  -- g ≠ 1 ⇒ λ(g) ≠ 0 --
  lambda_zero_one : ∀ g : M, lambda g = 0 ↔ g = 1
  -- (ii) Any two elements of M admit left- and right- lcms and gcds - defined in LeftRightGCDMonoid --
  -- (iii) Δ is a Garside element of M --
  Δ : M
  -- meaning that the left- and right- divisors of Δ coincide --
  div_Δ_left_right : ∀ g : M, g ≼ₗ Δ ↔ g ≼ᵣ Δ
  div_Δ : Set M := {g | g ≼ₗ Δ}
  div_Δ_def_as_eq : div_Δ = {g | g ≼ₗ Δ} := by eq_refl
  -- and generate M --
  div_Δ_gen : Submonoid.closure div_Δ = ⊤
  -- (iv) The family Div(Δ) of all divisors of Δ in M is finite --
  div_Δ_fin : Finite div_Δ

@[inherit_doc] prefix:100  "λ" => GarsideMonoid.lambda
@[inherit_doc] infix:80  "∧ₗ" => GarsideMonoid.left_gcd
@[inherit_doc] infix:80  "∧ᵣ" => GarsideMonoid.right_gcd
notation "Δ" => GarsideMonoid.Δ
notation "div_Δ" => GarsideMonoid.div_Δ

def my_set := { x : ℕ | x <= 3}

lemma bar (x : ℕ) : x ∈ my_set -> x <= 3 :=
  fun x => x

lemma bar' (x : ℕ) : x <= 3 -> x ∈ my_set :=
  fun x => x

lemma one_min_left_dvd [Monoid M] (a : M) : 1 ≼ₗ a :=
  ⟨a, one_mul _⟩

instance (M : Type*) [Monoid M] : IsRefl M LeftDvd.left_dvd where
  refl _ := ⟨1, mul_one _⟩

instance (M : Type*) [Semigroup M] : IsTrans M LeftDvd.left_dvd where
  trans := by
    intro a b c ⟨d, div_a_b⟩ ⟨e, div_b_c⟩
    rw [<-div_a_b, mul_assoc] at div_b_c
    exact ⟨d * e, div_b_c⟩

instance (M : Type*) [GarsideMonoid M] : IsAntisymm M LeftDvd.left_dvd where
  antisymm a b := by
    intro ⟨d, div_a_b⟩ ⟨e, div_b_a⟩
    have le_l_a_l_b : λ a ≤ λ b := calc
      λ a ≤ λ a + λ d := by
        simp
      _ ≤ λ b := by
        rw [<-div_a_b]
        exact (GarsideMonoid.lambda_ord _ _)
    have ge_l_a_add_l_b_l_e := (GarsideMonoid.lambda_ord b e)
    rw[div_b_a] at ge_l_a_add_l_b_l_e
    have le_l_e_zero : λ e ≤ 0 := by
      exact Nat.le_of_add_le_add_left (le_trans ge_l_a_add_l_b_l_e (le_l_a_l_b))
    have eq_l_e_zero : λ e = 0 := by
      exact Nat.eq_zero_of_le_zero le_l_e_zero
    have eq_e_one : e = 1 := by
      exact (GarsideMonoid.lambda_zero_one _).mp eq_l_e_zero
    rw [eq_e_one, mul_one, eq_comm] at div_b_a
    exact div_b_a

lemma lgcd_symm [GarsideMonoid M] (a b : M) : a ∧ₗ b = b ∧ₗ a := by
  apply @antisymm _ LeftDvd.left_dvd
  · apply GarsideMonoid.left_gcd_dvd
    · exact GarsideMonoid.left_gcd_dvd_right _ _
    · exact GarsideMonoid.left_gcd_dvd_left _ _
  · apply GarsideMonoid.left_gcd_dvd
    · exact GarsideMonoid.left_gcd_dvd_right _ _
    · exact GarsideMonoid.left_gcd_dvd_left _ _

lemma lgcd_assoc [GarsideMonoid M] (a b c : M) : (a ∧ₗ b) ∧ₗ c = a ∧ₗ (b ∧ₗ c) := by
  apply @antisymm _ LeftDvd.left_dvd
  · apply GarsideMonoid.left_gcd_dvd
    · calc (a∧ₗb)∧ₗc ≼ₗ (a∧ₗb) := GarsideMonoid.left_gcd_dvd_left _ _
          _ ≼ₗ a := GarsideMonoid.left_gcd_dvd_left _ _
    · apply GarsideMonoid.left_gcd_dvd
      · calc (a∧ₗb)∧ₗc ≼ₗ (a∧ₗb) := GarsideMonoid.left_gcd_dvd_left _ _
          _ ≼ₗ b := GarsideMonoid.left_gcd_dvd_right _ _
      · exact GarsideMonoid.left_gcd_dvd_right _ _
  · apply GarsideMonoid.left_gcd_dvd
    · apply GarsideMonoid.left_gcd_dvd
      · exact GarsideMonoid.left_gcd_dvd_left _ _
      · calc a∧ₗ(b∧ₗc) ≼ₗ (b∧ₗc) := GarsideMonoid.left_gcd_dvd_right _ _
          _ ≼ₗ b := GarsideMonoid.left_gcd_dvd_left _ _
    · calc a∧ₗ(b∧ₗc) ≼ₗ (b∧ₗc) := GarsideMonoid.left_gcd_dvd_right _ _
          _ ≼ₗ c := GarsideMonoid.left_gcd_dvd_right _ _

lemma mul_ldiv [GarsideMonoid M] (a b c: M) : b ≼ₗ c ↔ a * b ≼ₗ a * c := by
  constructor
  · intro ⟨x, eq_x⟩
    exists x
    rw[mul_assoc, eq_x]
  · intro ⟨x, eq_x⟩
    exists x
    rw[mul_assoc] at eq_x
    exact mul_left_cancel eq_x

lemma mul_ldiv_one [GarsideMonoid M] (a b: M) : b = 1 ↔ a * b ≼ₗ a := by
  constructor
  · intro eq_b
    exists 1
    rw[eq_b, mul_one, mul_one]
  · intro ldiv_prod_a
    nth_rewrite 2 [<-mul_one a] at ldiv_prod_a
    rw[<-mul_ldiv] at ldiv_prod_a
    apply @antisymm _ LeftDvd.left_dvd
    · exact ldiv_prod_a
    · exact one_min_left_dvd _

lemma lambda_str_incr_ldiv [GarsideMonoid M] :
    forall a b : M, a ≼ₗ b -> a ≠ b -> λ a < λ b := by
  rintro a b ⟨comp_a_b, decomp⟩ ne_a_b
  have lt_l_comp_0 : λ comp_a_b > 0 := by
    have ne_comp_a_b_1 : comp_a_b ≠ 1 := by
      by_cases is_eq_comp_a_b_1 : comp_a_b = 1
      · rw[is_eq_comp_a_b_1, mul_one] at decomp
        rcases ne_a_b decomp
      · exact is_eq_comp_a_b_1
    exact Nat.zero_lt_of_ne_zero
      (fun eq_0 => ne_comp_a_b_1
        ((GarsideMonoid.lambda_zero_one comp_a_b).mp eq_0))
  calc
    λ a < λ a + λ comp_a_b := by
      nth_rewrite 1 [<- add_zero (λ a)]
      exact Nat.add_lt_add_of_le_of_lt (le_refl _) lt_l_comp_0
    _ ≤ λ b := by
      rw[<- decomp]
      exact GarsideMonoid.lambda_ord _ _

lemma lambda_incr_ldiv [GarsideMonoid M] :
    forall a b : M, a ≼ₗ b -> λ a ≤ λ b := by
  rintro a b ⟨comp_a_b, decomp⟩
  calc
    λ a ≤ λ a + λ comp_a_b := by
      exact Nat.le_add_right (λa) (λcomp_a_b)
    _ ≤ λ b := by
      rw[<- decomp]
      exact GarsideMonoid.lambda_ord _ _

lemma lambda_str_incr_rdiv [GarsideMonoid M] :
    forall a b : M, a ≼ᵣ b -> a ≠ b -> λ a < λ b := by
  rintro a b ⟨comp_a_b, decomp⟩ ne_a_b
  have lt_l_comp_0 : λ comp_a_b > 0 := by
    have ne_comp_a_b_1 : comp_a_b ≠ 1 := by
      by_cases is_eq_comp_a_b_1 : comp_a_b = 1
      · rw[is_eq_comp_a_b_1, one_mul] at decomp
        rcases ne_a_b decomp
      · exact is_eq_comp_a_b_1
    exact Nat.zero_lt_of_ne_zero
      (fun eq_0 => ne_comp_a_b_1
        ((GarsideMonoid.lambda_zero_one comp_a_b).mp eq_0))
  calc
    λ a < λ comp_a_b + λ a := by
      nth_rewrite 1 [<- zero_add (λ a)]
      exact Nat.add_lt_add_of_lt_of_le lt_l_comp_0 (le_refl _)
    _ ≤ λ b := by
      rw[<- decomp]
      exact GarsideMonoid.lambda_ord _ _

lemma lambda_incr_rdiv [GarsideMonoid M] :
    forall a b : M, a ≼ᵣ b -> λ a ≤ λ b := by
  rintro a b ⟨comp_a_b, decomp⟩
  calc
    λ a ≤ λ comp_a_b + λ a := by
      exact Nat.le_add_left (λa) (λcomp_a_b)
    _ ≤ λ b := by
      rw[<- decomp]
      exact GarsideMonoid.lambda_ord _ _

instance {M : Type*} : Monoid (List M) where
  one := []
  mul := List.append
  mul_assoc := List.append_assoc
  mul_one := List.append_nil
  one_mul := List.nil_append

inductive SimpleList [GarsideMonoid M] : List M -> Prop where
  | simple_nil : SimpleList []
  | simple_cons (s : M) (l : List M) :
    (s ∈ div_Δ) -> s ≠ 1 -> SimpleList l -> SimpleList (s :: l)

lemma simple_prod [GarsideMonoid M] (l m : List M) :
  SimpleList l -> SimpleList m -> SimpleList (l * m) := by
  intro smpl_l smpl_m
  induction smpl_l with
  | simple_nil =>
    rw[(by eq_refl : [] * m = [] ++ m)]
    dsimp
    exact smpl_m
  | simple_cons s l div_s_Δ ne_s_one _ ih =>
    exact SimpleList.simple_cons s (l ++ m) div_s_Δ ne_s_one ih

def π_fun [Monoid M] : List M -> M :=
  fun
    | [] =>
      1
    | a :: t =>
      a * π_fun t

def π [Monoid M] : List M →* M where
  toFun :=
    π_fun
  map_one' :=
    by dsimp!
  map_mul' := by
    intro l m
    rw[(by rfl : l * m = l ++ m)]
    dsimp!
    induction l with
    | nil =>
      dsimp!
      rw[eq_comm]
      exact one_mul _
    | cons h t tih =>
      dsimp!
      rw[tih, <- mul_assoc]

lemma exists_simple_decomp [GarsideMonoid M] :
    ∀ a : M, ∃ l : List M, SimpleList l ∧ π l = a := by
  intro a
  have foo : a ∈ Submonoid.closure div_Δ := by
    rw [GarsideMonoid.div_Δ_gen]
    trivial
  induction foo using Submonoid.closure_induction with
  | mem x h =>
    by_cases val_x : x = 1
    · constructor
      constructor
      · exact SimpleList.simple_nil
      · rw[val_x]
        trivial
    · constructor
      constructor
      · apply SimpleList.simple_cons
        · exact h
        · exact val_x
        · exact SimpleList.simple_nil
      · exact (mul_one x)
  | one =>
    constructor
    constructor
    · exact SimpleList.simple_nil
    · trivial
  | mul x y _ _ ex_x ex_y =>
    rcases ex_x, ex_y with ⟨⟨lx, ⟨smpl_lx, prod_x⟩⟩, ⟨ly, ⟨smpl_ly, prod_y⟩⟩⟩
    constructor
    constructor
    · exact (simple_prod _ _ smpl_lx smpl_ly)
    · rw[map_mul _ _, prod_x, prod_y]

inductive DeltaNormal [GarsideMonoid M] : List M -> Prop where
  | delta_normal_nil : DeltaNormal []
  | delta_normal_cons (s : M) (d : List M) :
    s = Δ ∧ₗ π (s :: d) -> s ≠ 1 -> DeltaNormal d ->
    DeltaNormal (s :: d)

lemma delta_normal_on_length [GarsideMonoid M] :
  ∀ l : ℕ, ∀ u : M, λ u = l -> ∃ d : List M,
    DeltaNormal d ∧ π d = u ∧
    (∀ e : List M, DeltaNormal e -> π e = u -> e = d) := by
  intro l
  induction l using Nat.strongRec with
  | ind l ih =>
    rcases l with (_ | ⟨l⟩)
    · intro u eq_u_one
      rw[GarsideMonoid.lambda_zero_one] at eq_u_one
      constructor
      constructor
      · exact DeltaNormal.delta_normal_nil
      · constructor
        · rw [eq_u_one]
          trivial
        · rintro (_ | ⟨h, t⟩)
          · intro _ _
            eq_refl
          · rintro left right
            rcases left with (_ | ⟨_, _, b, ne_h_one, d⟩)
            rw[(by eq_refl : π (h :: t) = π_fun (h :: t))] at right
            dsimp! at right
            rw[<-(by eq_refl : π t = π_fun t), eq_u_one] at right
            have eq_l_h_0 : λ h ≤ 0 := by
              rw[
                <-((GarsideMonoid.lambda_zero_one (1 : M)).mpr
                (by eq_refl : (1 : M) = 1) : λ (1 : M) = 0)
              ]
              exact lambda_incr_ldiv _ _ ⟨π t, right⟩
            apply Nat.eq_zero_of_le_zero at eq_l_h_0
            rcases (ne_h_one ((GarsideMonoid.lambda_zero_one h).mp eq_l_h_0))
    · intro u eq_l_u_succ_l
      have ⟨rcomp, decomp⟩ := GarsideMonoid.left_gcd_dvd_right Δ u
      have lgcd_non_trivial : Δ ∧ₗ u ≠ 1 := by
        have ⟨l_u, ⟨smpl_l_u, prod_u⟩⟩ := exists_simple_decomp u
        rw[(by eq_refl : π l_u = π_fun l_u)] at prod_u
        rcases smpl_l_u with (_ | ⟨s, t, smpl_s, ne_s_one, _⟩)
        · dsimp! at prod_u
          rw[eq_comm] at prod_u
          rw[prod_u, (GarsideMonoid.lambda_zero_one 1).mpr (by rfl)] at eq_l_u_succ_l
          trivial
        · dsimp! at prod_u
          have ldiv_s_lgcd : s ≼ₗ Δ ∧ₗ u := by
            apply GarsideMonoid.left_gcd_dvd
            · rw[GarsideMonoid.div_Δ_def_as_eq] at smpl_s
              exact smpl_s
            · exact ⟨_, prod_u⟩
          dsimp!
          intro eq_lgcd_one
          have eq_s_one : s = 1 := by
            apply @antisymm _ LeftDvd.left_dvd
            · rw[eq_lgcd_one] at ldiv_s_lgcd
              exact ldiv_s_lgcd
            · exact (one_min_left_dvd s)
          exact ne_s_one eq_s_one
      have lt_l_rcomp_s_l : λ rcomp < l + 1 := by
        rw[<- eq_l_u_succ_l]
        have ne_rcomp_u : rcomp ≠ u := by
          intro eq_rcomp_u
          rw[<- one_mul rcomp] at eq_rcomp_u
          exact lgcd_non_trivial (CancelMonoid.mul_right_cancel _ _ _
          (by
            rw[eq_rcomp_u]
            exact decomp))
        exact lambda_str_incr_rdiv rcomp u ⟨Δ ∧ₗ u, decomp⟩ ne_rcomp_u
      have ⟨d, ⟨delnorm_d, ⟨prod_rcomp, d_unique⟩⟩⟩ :=
        ih (λ rcomp) lt_l_rcomp_s_l rcomp (by rfl)
      exists (Δ ∧ₗ u :: d)
      constructor
      · apply DeltaNormal.delta_normal_cons (Δ ∧ₗ u) d
        -- We want to use (Δ ∧ₗ u) :: d (should be that given the definition of the Δ-normal form) --
        · rw[(by eq_refl : π (Δ∧ₗu :: d) = π_fun (Δ∧ₗu :: d))]
          dsimp!
          rw[<- (by eq_refl : π d = π_fun d), prod_rcomp, decomp]
        · exact lgcd_non_trivial
        · exact delnorm_d
      · constructor
        · rw[(by eq_refl : π (Δ∧ₗu :: d) = π_fun (Δ∧ₗu :: d))]
          dsimp!
          rw[<- (by eq_refl : π d = π_fun d), prod_rcomp, decomp]
        · rintro e (_ | ⟨a, e, eq_a_lgcd, ne_a_one, delnorm_e⟩) eq_pi_e_u
          · rw[(by eq_refl : π [] = π_fun [])] at eq_pi_e_u
            dsimp! at eq_pi_e_u
            rw[<- eq_pi_e_u, (GarsideMonoid.lambda_zero_one (1: M)).mpr (by eq_refl)] at eq_l_u_succ_l
            trivial
          · rw[List.cons_eq_cons]
            rewrite[eq_pi_e_u] at eq_a_lgcd
            constructor
            · exact eq_a_lgcd
            · apply d_unique e delnorm_e
              · rw[(by eq_refl : π (a :: e) = π_fun (a :: e))] at eq_pi_e_u
                dsimp! at eq_pi_e_u
                rw[<- (by eq_refl : π e = π_fun e)] at eq_pi_e_u
                rw[<- eq_a_lgcd] at decomp
                rw[<- decomp] at eq_pi_e_u
                exact LeftCancelMonoid.mul_left_cancel a _ _ eq_pi_e_u

theorem delta_normal_form_exists [GarsideMonoid M] :
  ∀ u : M, ∃ d : List M,
    DeltaNormal d ∧ π d = u ∧
    (∀ e : List M, DeltaNormal e -> π e = u -> e = d) := by
  intro u
  exact delta_normal_on_length (λ u) u (by eq_refl)

inductive LocalDeltaNormal [GarsideMonoid M] : List M -> Prop where
  | delta_normal_nil : LocalDeltaNormal []
  | delta_normal_simple (s : M) :
    s ∈ div_Δ -> s ≠ 1 ->
    LocalDeltaNormal (s :: [])
  | delta_normal_cons (s t : M) (d : List M) :
    s = Δ ∧ₗ (s * t) -> LocalDeltaNormal (t :: d) ->
    LocalDeltaNormal (s :: t :: d)

lemma lgcd_lprod [GarsideMonoid M] (u v w : M) :
    (u * v) ∧ₗ (u * w) = u * (v ∧ₗ w) := by
  have ⟨x, eq_x⟩ : u ≼ₗ (u * v)∧ₗ(u * w) := by
    apply GarsideMonoid.left_gcd_dvd
    · exact ⟨v, by eq_refl⟩
    · exact ⟨w, by eq_refl⟩
  have ldiv_x_v : x ≼ₗ v := by
    have ⟨y, eq_y⟩ := (GarsideMonoid.left_gcd_dvd_left (u * v) (u * w))
    rw[<- eq_x, mul_assoc] at eq_y
    exists y
    apply mul_left_cancel at eq_y
    exact eq_y
  have ldiv_x_w : x ≼ₗ w := by
    have ⟨y, eq_y⟩ := (GarsideMonoid.left_gcd_dvd_left (u * w) (u * v))
    rw[lgcd_symm, <- eq_x, mul_assoc] at eq_y
    exists y
    apply mul_left_cancel at eq_y
    exact eq_y
  have ldiv_x_lgcd := GarsideMonoid.left_gcd_dvd x v w ldiv_x_v ldiv_x_w
  rw[<-eq_x]
  have eq_x_lgcd : x = v ∧ₗ w := by
    apply @antisymm _ LeftDvd.left_dvd
    · exact ldiv_x_lgcd
    · have ldiv_u_v : u * v∧ₗw ≼ₗ u * v := by
        have ⟨y, eq_y⟩ := GarsideMonoid.left_gcd_dvd_left v w
        nth_rewrite 2 [<-eq_y]
        rw[<- mul_assoc]
        exists y
      have ldiv_u_w : u * v∧ₗw ≼ₗ u * w := by
        have ⟨y, eq_y⟩ := GarsideMonoid.left_gcd_dvd_left w v
        nth_rewrite 2 [<-eq_y]
        rw[<- mul_assoc]
        exists y
        rw[lgcd_symm]
      have u_v_w : u * v∧ₗw ≼ₗ (u * v)∧ₗ(u * w) := by
        apply GarsideMonoid.left_gcd_dvd
        · exact ldiv_u_v
        · exact ldiv_u_w
      rw[<-eq_x] at u_v_w
      have ⟨y, eq_y⟩ := u_v_w
      exists y
      rw[mul_assoc] at eq_y
      exact mul_left_cancel eq_y
  rw[eq_x_lgcd]

lemma alt_left [GarsideMonoid M] (u v w : M) :
    u * v = Δ -> (Δ ∧ₗ (u * w) = u ↔ v ∧ₗ w = 1) := by
  intro eq_prod_u_v_delta
  constructor
  · intro eq_lgcd_u
    rw[<-eq_prod_u_v_delta, lgcd_lprod] at eq_lgcd_u
    nth_rewrite 2 [<- mul_one u] at eq_lgcd_u
    exact mul_left_cancel eq_lgcd_u
  · intro eq_lgcd_1
    rw[<-eq_prod_u_v_delta, lgcd_lprod, eq_lgcd_1, mul_one]

theorem delta_normal_form_is_local [GarsideMonoid M] :
  ∀ d : List M, DeltaNormal d ↔ LocalDeltaNormal d := by
  intro d
  constructor
  · intro delnorm_d
    induction delnorm_d with
    | delta_normal_nil =>
      exact LocalDeltaNormal.delta_normal_nil
    | delta_normal_cons s d eq_s_lgcd ne_s_1 delnorm_d loc_delnorm_d =>
      rcases delnorm_d with _ | ⟨t, e, eq_t_lgcd, ne_t_1, delnorm_e⟩
      · apply LocalDeltaNormal.delta_normal_simple
        · rw[eq_s_lgcd, GarsideMonoid.div_Δ_def_as_eq]
          dsimp
          exact GarsideMonoid.left_gcd_dvd_left _ _
        · exact ne_s_1
      · apply LocalDeltaNormal.delta_normal_cons
        · rw[(by eq_refl : π (s :: t :: e) = π_fun (s :: t :: e))] at eq_s_lgcd
          dsimp! at eq_s_lgcd
          rw[<- mul_assoc] at eq_s_lgcd
          apply @antisymm _ LeftDvd.left_dvd
          · apply GarsideMonoid.left_gcd_dvd
            · rw[eq_s_lgcd]
              exact GarsideMonoid.left_gcd_dvd_left _ _
            · exact ⟨t, by eq_refl⟩
          · nth_rewrite 2 [eq_s_lgcd]
            apply GarsideMonoid.left_gcd_dvd
            · exact GarsideMonoid.left_gcd_dvd_left _ _
            · calc
              Δ∧ₗ(s * t) ≼ₗ s * t := by
                exact GarsideMonoid.left_gcd_dvd_right _ _
              _ ≼ₗ s * t * π_fun e :=
                ⟨π_fun e, by eq_refl⟩
        · exact loc_delnorm_d
  · intro locdelnorm_d
    induction locdelnorm_d with
    | delta_normal_nil =>
      exact DeltaNormal.delta_normal_nil
    | delta_normal_simple s le_s_delta ne_s_1 =>
      apply DeltaNormal.delta_normal_cons
      · rw[(by eq_refl : π (s :: []) = π_fun (s :: []))]
        dsimp!
        rw[mul_one]
        apply @antisymm _ LeftDvd.left_dvd
        · apply GarsideMonoid.left_gcd_dvd
          · rw[GarsideMonoid.div_Δ_def_as_eq] at le_s_delta
            exact le_s_delta
          · exact refl _
        · exact GarsideMonoid.left_gcd_dvd_right _ _
      · exact ne_s_1
      · exact DeltaNormal.delta_normal_nil
    | delta_normal_cons s t e eq_s_lgcd locdelnorm_cons_t_e delnorm_cons_t_e =>
      apply DeltaNormal.delta_normal_cons
      · rw[(by eq_refl : π (s :: t :: e) = π_fun (s :: t :: e))]
        dsimp!
        have ⟨y, eq_y⟩ := GarsideMonoid.left_gcd_dvd_left Δ (s * t)
        rw[<- eq_s_lgcd] at eq_y
        rw[eq_comm, alt_left s y _ eq_y]
        apply @antisymm _ LeftDvd.left_dvd
        · have ldiv_y_delta : y ≼ₗ Δ :=
            by
              rw[GarsideMonoid.div_Δ_left_right]
              exists s
          rcases delnorm_cons_t_e with _ | ⟨_, _, eq_t, ne_t_1, delnorm_e⟩
          rw[(by eq_refl : π (t :: e) = π_fun (t :: e))] at eq_t
          dsimp! at eq_t
          have foo : y∧ₗ(t * π_fun e) ≼ₗ t := by
            nth_rewrite 2 [eq_t]
            apply GarsideMonoid.left_gcd_dvd
            · calc
                y∧ₗ(t * π_fun e) ≼ₗ y := GarsideMonoid.left_gcd_dvd_left _ _
                _ ≼ₗ Δ := ldiv_y_delta
            · exact GarsideMonoid.left_gcd_dvd_right _ _
          have bar : y∧ₗ(t * π_fun e) = t∧ₗ (y∧ₗ(t * π_fun e)) := by
            apply @antisymm _ LeftDvd.left_dvd
            · apply GarsideMonoid.left_gcd_dvd
              · exact foo
              · exact refl _
            · apply GarsideMonoid.left_gcd_dvd
              · calc
                t∧ₗ(y∧ₗ(t * π_fun e)) ≼ₗ y∧ₗ(t * π_fun e) :=
                  GarsideMonoid.left_gcd_dvd_right _ _
                _ ≼ₗ y :=
                  GarsideMonoid.left_gcd_dvd_left _ _
              · calc
                t∧ₗ(y∧ₗ(t * π_fun e)) ≼ₗ y∧ₗ(t * π_fun e) :=
                  GarsideMonoid.left_gcd_dvd_right _ _
                _ ≼ₗ t * π_fun e :=
                  GarsideMonoid.left_gcd_dvd_right _ _
          rw[eq_comm, alt_left _ _ _ eq_y, lgcd_symm] at eq_s_lgcd
          rw[bar, <-lgcd_assoc, eq_s_lgcd]
          exact GarsideMonoid.left_gcd_dvd_left _ _
        · exact one_min_left_dvd _
      · intro eq_s_1
        rcases delnorm_cons_t_e with _ | ⟨_, _, eq_t, ne_t_1, _⟩
        rw[eq_s_1, one_mul, eq_comm] at eq_s_lgcd
        have eq_lgcd_t : Δ∧ₗt = t := by
          apply @antisymm _ LeftDvd.left_dvd
          · exact GarsideMonoid.left_gcd_dvd_right _ _
          · apply GarsideMonoid.left_gcd_dvd
            · rw[eq_t]
              exact GarsideMonoid.left_gcd_dvd_left _ _
            · exact refl _
        rw[eq_lgcd_t] at eq_s_lgcd
        exact ne_t_1 eq_s_lgcd
      · exact delnorm_cons_t_e
