import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
attribute [-simp] AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve IsLocalRing

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ₀ : A.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hx : (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    letI := ((residue ↥A).comp ρ₀).toAlgebra
    ∃ (V : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
      (hRV : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r ∈ V)
      (ρ : ↥V →+* LaurentSeries (ResidueField ↥A)),
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) (p : ↥(GaloisRep.ratLocalizedAt p)) ∈ V.nonunits ∧
      (∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p), ¬ (Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)) ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ v : ↥V, (v : ↥(qExpFunctionFieldC ℚ Γ)) ∈ V.nonunits → ρ v = 0) ∧
      (∀ r : ↥(GaloisRep.ratLocalizedAt p),
        ρ ⟨algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r, hRV r⟩ =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) r)) ∧
      (∀ v : ↥V, (v : ↥(qExpFunctionFieldC ℚ Γ)) = j → ρ v = jqModC (ResidueField ↥A)) ∧
      IntermediateField.adjoin (ResidueField ↥A) (Set.range ρ) = qExpFunctionFieldC (ResidueField ↥A) Γ ∧
      (∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ V ↔
        ∃ y z : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧
          coeffEmb (AlgebraicClosure ℚ) ((f : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * coeffMap A.subtype y =
            coeffMap A.subtype z) ∧
      (∀ (v : ↥V) (y z : LaurentSeries ↥A), coeffMap (residue ↥A) y ≠ 0 →
          coeffEmb (AlgebraicClosure ℚ) (((v : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) * coeffMap A.subtype y =
            coeffMap A.subtype z →
        ρ v * coeffMap (residue ↥A) y = coeffMap (residue ↥A) z) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime.solution
