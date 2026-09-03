import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss
set_option autoImplicit false

open scoped Polynomial

universe u

theorem ValuationSubring.finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (V : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)

    (𝔽 : Type u) [Field 𝔽] [Algebra R 𝔽] (h𝔽 : Function.Surjective (algebraMap R 𝔽))
    [Algebra 𝔽 (IsLocalRing.ResidueField ↥V)]
    (hcomp : ∀ r : R, algebraMap 𝔽 (IsLocalRing.ResidueField ↥V) (algebraMap R 𝔽 r) =
      IsLocalRing.residue ↥V ⟨algebraMap R F r, hRV r⟩)
    (jV : ↥V) (hjV' : (jV : F) = j) :

    FiniteDimensional
        ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))
        (IsLocalRing.ResidueField ↥V) ∧
    Module.finrank
        ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))
        (IsLocalRing.ResidueField ↥V) ≤
      Module.finrank ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F ∧

    (Module.finrank ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F ≤
        Module.finrank
          ↥(IntermediateField.adjoin 𝔽 ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V)))
          (IsLocalRing.ResidueField ↥V) →
      (∀ f : F, f ∈ V.nonunits → f * (algebraMap R F ϖ)⁻¹ ∈ V) ∧
      (∀ V' : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V') → algebraMap R F ϖ ∈ V'.nonunits →
        (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') → V' = V)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss.solution
