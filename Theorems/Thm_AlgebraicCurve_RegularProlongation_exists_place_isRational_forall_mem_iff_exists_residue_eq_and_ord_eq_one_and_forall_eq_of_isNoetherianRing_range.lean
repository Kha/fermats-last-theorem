import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (𝒩 : Subring F) [IsLocalRing ↥𝒩]
    (h𝒩 : ∀ f : F, f ∈ 𝒩 → f ∈ R.integers)

    (hA : ∀ a : ↥A, algebraMap L F (a : L) ∈ 𝒩)
    (hres : ∀ g : ↥𝒩, ∃ a : ↥A, ¬ IsUnit (g - ⟨algebraMap L F (a : L), hA a⟩))

    (y : ↥𝒩) (hyu : ¬ IsUnit y) (hy0 : R.residue ⟨(y : F), h𝒩 y y.2⟩ ≠ 0)

    (hmax : ∀ f : ↥𝒩, ¬ IsUnit f →
      ∃ g h : ↥𝒩, R.residue ⟨(h : F), h𝒩 h h.2⟩ = 0 ∧ f = y * g + h)

    (hnoeth : IsNoetherianRing
      ↥(R.residue.comp (Subring.inclusion (show 𝒩 ≤ R.integers.toSubring from fun f hf => h𝒩 f hf))).range)

    (hfrac : ∀ z : Fbar, ∃ f g : ↥𝒩, R.residue ⟨(g : F), h𝒩 g g.2⟩ ≠ 0 ∧
      z * R.residue ⟨(g : F), h𝒩 g g.2⟩ = R.residue ⟨(f : F), h𝒩 f f.2⟩) :
    ∃ x₁ : Place (ResidueField A) Fbar,
      x₁.IsRational ∧

      (∀ z : Fbar, z ∈ x₁.toValuationSubring ↔ ∃ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ = z) ∧

      (∀ f : ↥𝒩, ¬ IsUnit f → R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring.nonunits) ∧
      (∀ f : ↥𝒩, ¬ IsUnit f → R.residue ⟨(f : F), h𝒩 f f.2⟩ ≠ 0 →
        0 < x₁.ord (R.residue ⟨(f : F), h𝒩 f f.2⟩)) ∧

      x₁.ord (R.residue ⟨(y : F), h𝒩 y y.2⟩) = 1 ∧

      (∀ (f : ↥𝒩) (a : ↥A), ¬ IsUnit (f - ⟨algebraMap L F (a : L), hA a⟩) →
        ∀ m : R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring,
          IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m⟩ =
            algebraMap (ResidueField A) x₁.ResidueField (IsLocalRing.residue ↥A a)) ∧

      (∀ Q' : Place (ResidueField A) Fbar,
        (∀ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ Q'.toValuationSubring) → Q' = x₁) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range.solution
