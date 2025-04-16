import Mathlib.SetTheory.Cardinal
import Mathlib.SetTheory.Ordinal
import Mathlib.SetTheory.Forcing
import Mathlib.Topology.Basic
import Mathlib.Topology.RegularOpen
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice

noncomputable section

attribute [instance] classical.prop_decidable
attribute [simp] omega_le_aleph

local infix:65 " ⟹ " => lattice.imp
local infix:50 " ⇔ " => lattice.biimp
local prefix:70 "#"   => cardinal.mk
local infix:75 "≺"  => (λ x y, -(larger_than x y))
local infix:75 "≼"  => (λ x y, injects_into x y)

universe u

namespace bSet

section cardinal_preservation
  local notation "ω" => cardinal.omega
  variables {𝔹 : Type u} [I : nontrivial_complete_boolean_algebra 𝔹]
  include I

  lemma AE_of_check_larger_than_check'' {x y : pSet.{u}} (f : bSet 𝔹) {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ is_surj_onto x̌ y̌ f)
    (H_nonempty : ∃ z, z ∈ y) :
    ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair (x.func j)̌ (y.func i)̌ ∈ᴮ f) :=
  begin
    intro i_v, bv_split_at H,
    replace H_right := H_right (y.func i_v)̌,
    simp [check_mem'] at H_right,
    replace H_right := exists_convert H_right _,
    cases H_right with w Hw, bv_split_at Hw,
    rcases eq_check_of_mem_check ‹_› Hw_left with ⟨j, Γ', HΓ'₁, HΓ'₂, H_eq⟩,
    use j,
    refine lt_of_lt_of_le HΓ'₁ (le_inf _ _),
    { exact le_trans HΓ'₂ (is_func_of_is_func' ‹_›) },
    { apply @bv_rw' _ _ _ _ _ (bv_symm H_eq) (λ z, pair z (y.func i_v)̌ ∈ᴮ f),
      exact B_ext_pair_mem_left,
      from le_trans ‹_› ‹_› },
    exact B_ext_inf (by simp) B_ext_pair_mem_left
  end

  lemma AE_of_check_larger_than_check' {x y : pSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ surjects_onto x̌ y̌)
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair (x.func j)̌ (y.func i)̌ ∈ᴮ f) :=
  begin
    unfold surjects_onto at H,
    have := maximum_principle (λ w, is_func' x̌ y̌ w ⊓ is_surj x̌ (y̌ : bSet 𝔹) w) _,
    cases this with f Hf, rw Hf at H, swap, { simp },
    exact ⟨f, AE_of_check_larger_than_check'' ‹_› ‹_› ‹_› ‹_›⟩
  end

  lemma AE_of_check_larger_than_check {x y : pSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ larger_than x̌ y̌)
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.type, ∃ j : x.type, ⊥ < (is_func f) ⊓ (pair (x.func j)̌ (y.func i)̌ ∈ᴮ f) :=
    AE_of_check_larger_than_check'
      ‹_› (surjects_onto_of_larger_than_and_exists_mem ‹_› $ by simp*) ‹_›

  variables
    (η₁ η₂ : pSet.{u})
    (H_infinite : ω ≤ #(η₁.type))
    (H_lt : #(η₁.type) < #(η₂.type))
    (H_inj₂ : ∀ x y, x ≠ y → ¬ pSet.equiv (η₂.func x) (η₂.func y))
    (f : bSet 𝔹)
    (g : η₂.type → η₁.type)
    (H : ∀ β : η₂.type,
         (⊥ : 𝔹) < is_func f ⊓ pair (η₁.func (g β))̌ ((η₂.func β)̌) ∈ᴮ f)

  include H_infinite H_lt H_inj₂ f H

  lemma not_CCC_of_uncountable_fiber (H_ex : ∃ ξ : η₁.type, ω < #(g⁻¹' {ξ})) :
    ¬ CCC 𝔹 :=
  begin
    cases H_ex with ξ H_ξ,
    let 𝓐 : (g⁻¹'{ξ}) → 𝔹 :=
      λ β, is_func f ⊓ (pair ((η₁.func (g β.val))̌) ((η₂.func β.val)̌)) ∈ᴮ f,
    have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β, from λ _, by apply H,
    have 𝓐_anti : ∀ β₁ β₂, β₁ ≠ β₂ → (𝓐 β₁) ⊓ (𝓐 β₂) ≤ ⊥,
    begin
      intros β₁ β₂ h_sep, dsimp [𝓐],
      /- `tidy_context` says -/
      apply poset_yoneda, intros Γ a,
      cases β₂, cases β₁, cases H_ξ, cases H_lt, cases β₁_property, cases β₂_property,
      work_on_goal 0 { induction β₂_property, simp only [le_inf_iff] at a,
                       cases a, cases a_right, cases a_left },
      work_on_goal 1 { induction β₁_property, simp only [le_inf_iff] at a,
                       cases a, cases a_right, cases a_left, solve_by_elim },
      work_on_goal 1 { cases β₂_property,
        work_on_goal 0 { induction β₂_property, simp only [le_inf_iff] at a,
          cases a, cases a_right, cases a_left, solve_by_elim }, simp only [le_inf_iff] at a,
          cases a, cases a_right, cases a_left, solve_by_elim },
      rw [β₁_property] at a_left_right,
      have H_le_eq : Γ ≤ ((η₂.func β₁_val)̌) =ᴮ ((η₂.func β₂_val)̌),
      by { apply eq_of_is_func_of_eq, from a_right_left, tactic.rotate 1,
           from ‹_›, from ‹_›, from bv_refl },
      exact le_trans H_le_eq (by { rw [le_bot_iff], apply check_bv_eq_bot_of_not_equiv,
        apply H_inj₂, tidy }),
    end,
    intro H_CCC, specialize H_CCC (g⁻¹'{ξ}) ‹_› ‹_› ‹_›,
    replace H_ξ := (lt_iff_le_and_ne.mp H_ξ),
    exact absurd (le_antisymm H_ξ.left H_CCC) H_ξ.right
  end

end cardinal_preservation

end bSet

open bSet

namespace pSet

@[reducible, noncomputable] def ℵ₁ : pSet.{0} := ordinal.mk (aleph 1).ord
@[reducible, noncomputable] def ℵ₂ : pSet.{0} := ordinal.mk (aleph 2).ord

lemma ℵ₂_unfold : ℵ₂ = ⟨ℵ₂.type, ℵ₂.func⟩ := by cases ℵ₂; rfl

@[simp, cleanup] lemma Union_type {x : pSet} :
  (type (Union x)) = Σ (a : x.type), (x.func a).type :=
by induction x; rfl

@[simp, cleanup] lemma Union_type' {α : Type u} {A : α → pSet.{u}} :
  (Union (mk α A)).type = Σ a, (A a).type := rfl

end pSet

open pSet

def 𝔹_cohen : Type :=
  @regular_opens (Set (ℵ₂.type × ℕ)) (Pi.topological_space)

local notation "𝔹" => 𝔹_cohen

instance H_nonempty : nonempty (Set (ℵ₂.type × ℕ)) := ⟨∅⟩

@[instance, priority 1000] def 𝔹_boolean_algebra : nontrivial_complete_boolean_algebra 𝔹 :=
  regular_open_algebra

lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.val ⊆ y.val := by rfl
lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, is_regular_empty⟩ := rfl

private lemma eq₀ : ((ℵ₂̌ : bSet 𝔹).type) = (ℵ₂).type :=
by cases ℵ₂; rfl

private lemma eq₁ : ((type (ℵ₂̌ : bSet 𝔹)) × ℕ) = ((type ℵ₂) × ℕ) :=
by { cases ℵ₂, rfl }

private lemma eq₂ : Set ((type (ℵ₂̌ : bSet 𝔹)) × ℕ) = Set ((type ℵ₂) × ℕ) :=
by { cases ℵ₂, rfl }

private lemma eq₃ : Finset ((type (ℵ₂̌ : bSet 𝔹)) × ℕ) = Finset ((type ℵ₂) × ℕ) :=
by { cases ℵ₂, rfl }

lemma pi₂_cast₁ {α β γ : Type*} (H' : α = β) {p : α × γ} {q : β × γ} (H : p == q) :
  p.fst == q.fst :=
by { subst H', subst H }

lemma pi₂_cast₂ {α β γ : Type*} (H' : α = β) {p : α × γ} {q : β × γ} (H : p == q) :
  p.snd = q.snd :=
by { subst H', subst H }

lemma compl_cast₂ {α β : Type*} {a : Set α} {b : Set β} (H' : α = β) (H : -a == b) :
  a == -b :=
begin
  subst H', subst H, exact heq_of_eq (by simp)
end

lemma eq₁_cast (p : ((type (ℵ₂̌ : bSet 𝔹)) × ℕ))
  {prf : ((type (ℵ₂̌ : bSet 𝔹)) × ℕ) = ((type ℵ₂) × ℕ)}
  {prf' : (type (ℵ₂̌ : bSet 𝔹)) = (ℵ₂.type)} :
  cast prf p = (cast prf' p.fst, p.snd) :=
begin
  ext, swap, simp,
  h_generalize H_x : p == x, apply pi₂_cast₂, exact eq₀.symm, exact H_x.symm,
  h_generalize H_x : p == x, simp,
  h_generalize H_y : p.fst == y,
  apply eq_of_heq,
  suffices : x.fst == p.fst, from heq.trans this H_y,
  apply pi₂_cast₁, exact eq₀.symm, exact H_x.symm,
end

lemma eq₁_cast' (p : ((type ℵ₂) × ℕ))
  {prf : ((type (ℵ₂̌ : bSet 𝔹)) × ℕ) = ((type ℵ₂) × ℕ)}
  {prf' : (type (ℵ₂̌ : bSet 𝔹)) = (ℵ₂.type)} :
  cast prf.symm p = (cast prf'.symm p.fst, p.snd) :=
begin
  ext, swap, simp,
  h_generalize H_x : p == x, apply pi₂_cast₂, exact eq₀, exact H_x.symm,
  h_generalize H_x : p == x, simp,
  h_generalize H_y : p.fst == y,
  apply eq_of_heq,
  suffices : x.fst == p.fst, from heq.trans this H_y,
  apply pi₂_cast₁, exact eq₀, exact H_x.symm,
end

theorem 𝔹_CCC : CCC 𝔹 :=
by { apply CCC_regular_opens, apply cantor_space.countable_chain_condition_set }

local notation "𝒳" => Set (ℵ₂.type × ℕ)

open topological_space

/-- The principal regular open associated to a pair (ν, n) is the collection of all subsets of
    ℵ₂ × ℕ which contain (ν, n). -/
def principal_open (ν : (ℵ₂̌ : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
begin
  use (cantor_space.principal_open (cast eq₁ (ν, n))),
  exact is_regular_of_clopen (cantor_space.is_clopen_principal_open)
end

lemma is_clopen_principal_open {ν n} : is_clopen (principal_open ν n).val :=
  cantor_space.is_clopen_principal_open

local postfix:80 "ᵖ" => perp
local notation "cl" => closure
local notation "int" => interior

lemma perp_eq_compl_of_clopen {β : Type*} [topological_space β] {S : Set β}
  (H : is_clopen S) : Sᵖ = (-S) :=
by { unfold perp, rw [closure_eq_of_is_closed H.right] }

lemma mem_neg_principal_open_of_not_mem {ν n S} :
  (cast eq₁ (ν, n) ∈ (-S)) → S ∈ (- (principal_open ν n)).val :=
begin
  intro H, simp only [neg_unfold],
  rw [perp_eq_compl_of_clopen],
  { exact H },
  { exact is_clopen_principal_open }
end

structure 𝒞 : Type :=
(ins : Finset ((ℵ₂̌ : bSet 𝔹).type × ℕ))
(out : Finset ((ℵ₂̌ : bSet 𝔹).type × ℕ))
(H : ins ∩ out = ∅)

@[reducible] def π₂ : ((ℵ₂̌ : bSet 𝔹).type × ℕ) → ℕ := λ x, x.snd

lemma to_set_inter {α : Type*} {p₁ p₂ : Finset α} :
  (p₁ ∩ p₂).toSet = (p₁.toSet ∩ p₂.toSet) :=
by { ext, split; intros; unfold Finset.toSet at *, tidy }

@[simp] lemma to_set_empty {α : Type*} :
  Finset.toSet (∅ : Finset α) = ∅ :=
by { unfold Finset.toSet, rfl }

lemma not_mem_of_inter_empty_left {α : Type*} {p₁ p₂ : Finset α}
  (H : p₁ ∩ p₂ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet :=
begin
  intro H', intro H'',
  have this₀ : a ∈ p₁.toSet ∩ p₂.toSet := ⟨H', H''⟩,
  rw [←to_set_inter] at this₀,
  have this₁ := congrArg Finset.toSet H,
  rw [this₁] at this₀, cases this₀,
end

lemma not_mem_of_inter_empty_right {α : Type*} {p₁ p₂ : Finset α}
  (H : p₂ ∩ p₁ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet :=
by { rw [Finset.inter_comm] at H, apply not_mem_of_inter_empty_left, exact H }

lemma 𝒞_nonzero (p : 𝒞) : ⊥ ≠ (ι p) :=
begin
  intro H, replace H := H.symm, rw [eq_bot_iff] at H, rw [le_iff_subset'] at H,
  rw [bot_eq_empty] at H,
  suffices : nonempty (ι p).val,
  { exact Classical.choice this; specialize H this.property; cases H },
  apply nonempty.intro, fsplit, exact cast eq₂ p.ins.toSet,
  split,
  { exact cast eq₂ p.ins.toSet },
  intro x, cases x with ν n, intro H,
  suffices : cast eq₁ (ν, n) ∈ - cast eq₂ (p.ins).toSet,
  { convert this, exact eq₀.symm, exact eq₀.symm, exact eq₀.symm, trivial, trivial },
  suffices : (ν, n) ∈ - p.ins.toSet,
  { convert this, exact eq₀.symm, exact eq₀.symm, exact eq₀.symm, trivial, exact eq₀.symm, trivial },
  exact not_mem_of_inter_empty_right p.H H
end

lemma subset_of_eq {α : Type*} {a b : Finset α} (H : a = b) : a ⊆ b :=
by rw [H]; rfl

lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : (ℵ₂̌ : bSet 𝔹).type,
  (cast eq₁.symm (ξ, n)) ∉ p.ins ∧ (cast eq₁.symm (ξ, n)) ∉ p.out :=
begin
  let Y := (Finset.image π₂ p.ins) ∪ (Finset.image π₂ p.out),
  by_cases (p.ins ∪ p.out) = ∅,
  { use 0, intro ξ, split,
    { intro x, apply (subset_of_eq h), simp, left, exact x },
    { intro x, apply (subset_of_eq h), simp, right, exact x } },
  let Y' := Finset.image π₂ (p.ins ∪ p.out),
  have Y'_nonempty : Y' ≠ ∅,
  { dsimp [Y'], intro H, apply h, ext; split; intros;
    { cases a_1, have : π₂ a ∈ Finset.image π₂ (p.ins ∪ p.out), simp,
      use a.fst, simp at a_1, convert a_1, cases a, rfl, cases a, rfl },
    rw [H] at this, cases this },
  have := Finset.max_of_ne_empty Y'_nonempty, cases this with N HN, swap, apply_instance,
  use (N+1), intro ξ, split,
  { intro X, let prf := _,
    change cast prf (ξ, N + 1) ∈ p.ins at X,
    rw [eq₁_cast'] at X, swap, exact eq₀,
    have : N + 1 ∈ Y',
    { simp, use cast eq₀.symm ξ, left, exact X },
    suffices : N + 1 ≤ N, by { revert this, exact Nat.not_succ_le_self N },
    exact Finset.le_max_of_mem this ‹_› },
  { intro X, let prf := _,
    change cast prf (ξ, N + 1) ∈ p.out at X,
    rw [eq₁_cast'] at X, swap, exact eq₀,
    have : N + 1 ∈ Y',
    { simp, use cast eq₀.symm ξ, right, exact X },
    suffices : N + 1 ≤ N, by { revert this, exact Nat.not_succ_le_self N },
    exact Finset.le_max_of_mem this ‹_› }
end

lemma 𝒞_anti {p₁ p₂ : 𝒞} :
  p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁ :=
by { intros H₁ H₂, rw [le_iff_subset'], tidy }

namespace cohen_real
section cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ induced by every ordinal less than ℵ₂. -/
def χ (ν : (ℵ₂̌ : bSet 𝔹).type) : ℕ → 𝔹 :=
  λ n, principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) induced by `cohen_real.χ ν`. -/
def mk (ν : (ℵ₂̌ : bSet 𝔹).type) : bSet 𝔹 :=
  @bSet.set_of_indicator 𝔹 _ ω (λ n, χ ν n.down)

@[simp, cleanup] lemma mk_type {ν} : (mk ν).type = Ulift ℕ := rfl
@[simp, cleanup] lemma mk_func {ν} {n} : (mk ν).func n = bSet.of_nat n.down := rfl
@[simp, cleanup] lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) n.down := rfl

/-- bSet 𝔹 believes that each `mk ν` is a subset of ω. -/
lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ ω :=
by simp [mk, subset_unfold]; exact (λ _, by rw [←deduction]; convert omega_definite)

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω). -/
lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset ω :=
bv_powerset_spec.mp definite

lemma sep {n} {Γ} {ν₁ ν₂}
  (H₁ : Γ ≤ (of_nat n) ∈ᴮ (mk ν₁))
  (H₂ : Γ ≤ (- ((of_nat n) ∈ᴮ (mk ν₂)))) :
  Γ ≤ (- ((mk ν₁) =ᴮ (mk ν₂))) :=
begin
  rw [bv_eq_unfold], rw [neg_inf, neg_infi, neg_infi], simp only [lattice.neg_imp],
  refine le_sup_left_of_le _,
  rw [@bounded_exists 𝔹 _ (mk ν₁) (λ z, - (z ∈ᴮ mk ν₂)) _],
  { change B_ext _, simp [-imp_bot, imp_bot.symm],
    apply bv_use (bSet.of_nat n), bv_split_goal,
  },
end

lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν, n) ∈ p.out) :
  ι p ≤ - ((of_nat n) ∈ᴮ (mk ν)) :=
begin
  rw [bSet.mem_unfold, neg_supr], bv_intro k, rw [neg_inf], simp,
  by_cases n = k.down, { rw [bSet.of_nat_inj ‹_›], exact le_sup_right_of_le (by simp) },
  refine le_sup_left_of_le _, rw [←h],
  rw [le_iff_subset'], unfold ι χ, rintros S ⟨H_S₁, H_S₂⟩,
  apply mem_neg_principal_open_of_not_mem, have := H_S₂ H, convert this,
  exact eq₀.symm, exact eq₀.symm, exact eq₀.symm,
  exact cast_heq _ _, exact (cast_heq _ _).symm,
end

private lemma inj_cast_lemma (ν' : (ℵ₂̌ : bSet 𝔹).type) (n' : ℕ) :
  cast eq₁.symm (cast eq₀ ν', n') = (ν', n') :=
begin
  let a := _,
  change cast a _ = _,
  let b := _,
  change cast _ (cast b _, _) = _,
  simp [b] at a, dedup,
  change cast a_1 _ = _,
  cc,
end

/-- Whenever ν₁ ≠ ν₂ (< ℵ₂), bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct. -/
lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : (mk ν₁) =ᴮ (mk ν₂) ≤ (⊥ : 𝔹) :=
begin
  by_contra,
  replace h := (bot_lt_iff_not_le_bot.mpr ‹_›),
  cases 𝒞_dense h with p H_p, cases 𝒞_disjoint_row p with n H_n,
  let p' : 𝒞 := { ins := insert (ν₁, n) (p.ins),
                   out := insert (ν₂, n) p.out,
                   H := by { ext, split; intro H,
                             { cases H, have := p.H, simp at H, cases a_1 with ν' n',
                               cases H with H₁ H₂, specialize H_n (cast eq₀ ν'),
                               cases H_n, cases H₁; cases H₂, cc,
                               exfalso, apply H_n_right, convert H₂, rw [show n = n', by cc],
                               apply inj_cast_lemma },
                             { exfalso, apply H_n_left, convert H₁, rw [show n = n', by cc],
                               apply inj_cast_lemma, rw [←this], simp [*,-this] } } },
  have this₀ : ι p' ≤ ι p,
    from 𝒞_anti (by { dsimp [p'], exact λ i _, by { simp, exact or.inr ‹_› } })
                (by { dsimp [p'], exact λ i _, by { simp, exact or.inr ‹_› } }),
  have this₁ : ι p' ≤ (ñ̌) ∈ᴮ (cohen_real.mk ν₁),
    by { rw [bSet.mem_unfold], apply bv_use (Ulift.up n), refine le_inf _ bv_refl,
         { simp [le_iff_subset', χ, _root_.principal_open, ι, cantor_space.principal_open],
           have : (ν₁, n) ∈ p'.ins,
           by simp [p'], intros S H_S, specialize H_S this,
           convert H_S; [exact eq₀.symm, exact eq₀.symm, exact eq₀.symm, trivial, trivial] } },
  have this₂ : ι p' ≤ - ((ñ̌) ∈ᴮ (cohen_real.mk ν₂)),
    by { have : (ν₂, n) ∈ p'.out, by simp [p'], exact not_mem_of_not_mem ‹_› },
  have this₃ : ι p' ≤ - ((mk ν₁) =ᴮ (mk ν₂)),
    from sep ‹_› ‹_›,
  have this₄ : ι p' ≤ (mk ν₁) =ᴮ (mk ν₂),
    from le_trans this₀ ‹_›,
  suffices : ι p' = ⊥, from absurd this.symm (𝒞_nonzero p'),
  bv_and_intro this₃ this₄, simpa using H,
end

end cohen_real
end cohen_real

section neg_CH

attribute [irreducible] regular_opens 𝔹_cohen

local notation "ℵ₀" := (omega : bSet 𝔹)
local notation "𝔠" := (bv_powerset ℵ₀ : bSet 𝔹)

lemma uncountable_fiber_of_regular' (κ₁ κ₂ : cardinal)
  (H_inf : cardinal.omega ≤ κ₁)
  (H_lt : κ₁ < κ₂)
  (H : cof (ord κ₂) = κ₂)
  (α : Type u) (H_α : #α = κ₁)
  (β : Type u) (H_β : #β = κ₂)
  (g : β → α) :
  ∃ (ξ : α), cardinal.omega < #↥(g⁻¹' {ξ}) :=
begin
  have := (@cardinal.exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)),
  cases this with k H_k, subst H_k,
  have := (@cardinal.exists_aleph κ₁).mp ‹_›,
  cases this with k' H_k', subst H_k',
  have := infinite_pigeonhole g _ _,
  cases this with ξ H_ξ, use ξ, rw [H_ξ],
  all_goals { simp* },
  exact lt_of_le_of_lt ‹_› ‹_›,
end

lemma uncountable_fiber_of_regular (κ₁ κ₂ : cardinal)
  (H_inf : cardinal.omega ≤ κ₁)
  (H_lt : κ₁ < κ₂)
  (H : cof (ord κ₂) = κ₂)
  (g : type (pSet.ordinal.mk (ord κ₂) : pSet.{u}) →
       type (pSet.ordinal.mk (ord κ₁) : pSet.{u})) :
  ∃ (ξ : type (pSet.ordinal.mk (ord κ₁))),
    cardinal.omega < #↥((λ (β : type (pSet.ordinal.mk (ord κ₂))), g β)⁻¹' {ξ}) :=
begin
  have := (@exists_aleph κ₁).mp ‹_›, cases this with k₁ h, subst h,
  have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)),
  cases this with k₂ h, subst h,
  exact uncountable_fiber_of_regular' (aleph k₁) (aleph k₂) ‹_› ‹_› ‹_› _ (by simp) _ (by simp) g,
end

lemma cardinal_inequality_of_regular (κ₁ κ₂ : cardinal)
  (H_reg₁ : cardinal.is_regular κ₁)
  (H_reg₂ : cardinal.is_regular κ₂)
  (H_inf : (omega : cardinal) ≤ κ₁)
  (H_lt : κ₁ < κ₂)
  {Γ : 𝔹} : Γ ≤ (card_ex κ₁)̌ ≺ (card_ex κ₂)̌ :=
begin
  dsimp only, rw [←imp_bot], bv_imp_intro H_larger_than,
  by_contra H_nonzero, rw [←bot_lt_iff_not_le_bot] at H_nonzero,
  rcases AE_of_check_larger_than_check H_nonzero ‹_› (exists_mem_of_regular ‹_›) with ⟨f, Hf⟩,
  rcases classical.axiom_of_choice Hf with ⟨g, g_spec⟩,
  suffices : ¬ CCC 𝔹, from absurd 𝔹_CCC this,
  apply not_CCC_of_uncountable_fiber; try { assumption },
  { have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k', simp* },
  { have := (@cardinal.exists_aleph κ₁).mp ‹_›, cases this with k' H_k', subst H_k', simp*,
    have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)),
    cases this with k₂ h, subst h, simp* },
  { intros i₁ i₂ H_neq, exact ordinal.mk_inj _ _ _ ‹_› },
  { dsimp at g,
    apply uncountable_fiber_of_regular' κ₁ κ₂; try { simp* },
    exact H_reg₂.right,
    have := (@exists_aleph κ₂).mp (le_of_lt (lt_of_le_of_lt ‹_› ‹_›)),
    cases this with k₂ h, subst h, apply mk_type_mk_eq, exact ‹_›,
    apply mk_type_mk_eq, exact le_of_lt (lt_of_le_of_lt ‹_› ‹_›) }
end

lemma ℵ₀_lt_ℵ₁ : (⊤ : 𝔹) ≤ ℵ₀ ≺ ℵ₁̌ :=
begin
  dsimp only, rw [←imp_bot], bv_imp_intro H_larger_than,
  by_contra H_nonzero, rw [←bot_lt_iff_not_le_bot] at H_nonzero,
  rcases AE_of_check_larger_than_check ‹_› ‹_› _ with ⟨f, Hf⟩,
  rcases classical.axiom_of_choice Hf with ⟨g, g_spec⟩,
  suffices : ¬ CCC 𝔹, from absurd 𝔹_CCC this,
  apply not_CCC_of_uncountable_fiber; try { assumption },
  { exact le_of_eq (by simp) },
  { simp },
  { intros i₁ i₂ H_neq, exact ordinal.mk_inj _ _ _ ‹_› },
  { dsimp at g,
    apply uncountable_fiber_of_regular' (aleph 0) (aleph 1); try { simp* },
    exact is_regular_aleph_one.right },
  { exact exists_mem_of_regular is_regular_aleph_one }
end

lemma ℵ₁_lt_ℵ₂ : (⊤ : 𝔹) ≤ ℵ₁̌ ≺ ℵ₂̌ :=
  cardinal_inequality_of_regular _ _ (is_regular_aleph_one)
    (is_regular_aleph_two) (by simp) (by simp)

lemma ℵ₁_lt_ℵ₂' {Γ : 𝔹} : Γ ≤ ℵ₁̌ ≺ ℵ₂̌ :=
  le_trans (le_top) ℵ₁_lt_ℵ₂

lemma cohen_real.mk_ext : ∀ (i j : type (ℵ₂̌ : bSet 𝔹)),
  func (ℵ₂̌) i =ᴮ func (ℵ₂̌) j ≤
  (λ (x : type (ℵ₂̌)), cohen_real.mk x) i =ᴮ (λ (x : type (ℵ₂̌)), cohen_real.mk x) j :=
begin
  intros i j, by_cases i = j,
  { simp [h] },
  { refine poset_yoneda _, intros Γ a, simp only [le_inf_iff] at *,
    have : func (ℵ₂̌) i = (ℵ₂.func (check_cast i))̌, by simp [check_func],
    rw [this] at a,
    have : func (ℵ₂̌) j = (ℵ₂.func (check_cast j))̌, by simp [check_func],
    rw [this] at a,
    suffices : (ℵ₂.func (check_cast i))̌ =ᴮ (ℵ₂.func (check_cast j))̌ ≤ ⊥,
      from le_trans a (le_trans this bot_le),
    rw [le_bot_iff], apply check_bv_eq_bot_of_not_equiv,
    apply ordinal.mk_inj, unfold check_cast, intro H, cc }
end

noncomputable def neg_CH_func : bSet 𝔹 :=
  @function.mk _ _ (ℵ₂̌) (λ x, cohen_real.mk x) cohen_real.mk_ext

theorem ℵ₂_le_𝔠 : ⊤ ≤ is_func' (ℵ₂̌) 𝔠 (neg_CH_func) ⊓ bSet.is_inj (neg_CH_func) :=
begin
  refine le_inf _ _,
  { unfold neg_CH_func, refine le_inf _ _, refine mk_is_func _ _,
    bv_intro w₁, bv_imp_intro, rw [bSet.mem_unfold] at H,
    bv_cases_at'' H ν, apply bv_use (cohen_real.mk ν),
    refine le_inf cohen_real.definite' _, swap,
    rw [bSet.mem_unfold], apply bv_use ν, bv_split,
    exact le_inf ‹_› (by apply le_trans H_1_right; from subst_congr_pair_left) },
  { refine mk_inj_of_inj _ _, exact λ _ _ _, cohen_real.inj ‹_› }
end

lemma ℵ₁_Ord {Γ : 𝔹} : Γ ≤ Ord (ℵ₁̌) := by simp
lemma ℵ₂_Ord {Γ : 𝔹} : Γ ≤ Ord (ℵ₂̌) := by simp

theorem neg_CH : (⊤ : 𝔹) ≤ -CH :=
begin
  dsimp [CH], rw [lattice.neg_neg],
  apply bv_use (ℵ₁̌),
  refine le_inf (ℵ₁_Ord) _,
  apply bv_use (ℵ₂̌),
  refine le_inf (le_inf _ _) _,
  { exact ℵ₀_lt_ℵ₁ },
  { exact ℵ₁_lt_ℵ₂ },
  { apply bv_use neg_CH_func, exact ℵ₂_le_𝔠 }
end

theorem neg_CH₂ : (⊤ : 𝔹) ≤ -CH₂ :=
  (bv_iff.neg $ @CH_iff_CH₂ _ _).mp neg_CH

end neg_CH
