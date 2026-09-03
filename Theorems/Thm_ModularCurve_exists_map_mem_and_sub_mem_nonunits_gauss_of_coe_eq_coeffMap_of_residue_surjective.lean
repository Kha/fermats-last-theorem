import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
attribute [-simp] AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap

set_option autoImplicit false

p2m_open "ModularCurve~exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq"

theorem ModularCurve.exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (hκ₁ : Function.Surjective
      (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ (a : ↥K₁)).mp a.2⟩))
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))
    (hK : K = ModularCurve.laurentBaseChange ↥K₁ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))

    (O : ValuationSubring ↥E)
    (hO : ∀ f : ↥E, f ∈ O ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (φ : ↥K →+* ↥E)
    (hφ : ∀ f : ↥K, ((φ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁)) :
    ∀ f : ↥E, f ∈ O → ∃ w : ↥K, φ w ∈ O ∧ (f - φ w : ↥E) ∈ O.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective.solution
