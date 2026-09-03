import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
import P2M.Util
namespace P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_forall_valuationSubring_mem

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (u : F) (m : ℕ)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∈ V → u ∈ V)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∉ V →
      u * ((x : F) ^ m)⁻¹ ∈ V)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → u ∈ V)
    (huO : u ∈ R.integers)
    (w : Place (IsLocalRing.ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue x)) ≤ w.ord (R.residue ⟨u, huO⟩) := by
  obtain ⟨p, hp, hdeg, hroot⟩ :=
    RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
      A R x hx u m h₁ h₂ h₃
  exact RegularProlongation.mul_min_ord_residue_le_of_monic A R x ⟨u, huO⟩ m p hp hdeg hroot w
