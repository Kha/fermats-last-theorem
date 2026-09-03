import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective

set_option autoImplicit false

p2m_open "ModularCurve~exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC~mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap~exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective AlgebraicCurve IsLocalRing"

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁]

    (hκ₁ : Function.Surjective
      (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ (a : ↥K₁)).mp a.2⟩))
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))
    (hK : K = ModularCurve.laurentBaseChange ↥K₁ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    [Algebra ↥A₁ ↥K] [IsScalarTower ↥A₁ ↥K₁ ↥K]
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))

    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A ↥E Fbar)
    (hO : ∀ f : ↥E, f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (T : Type) [Field T] [Algebra ↥A₁ T] [Algebra ↥K₁ T] [IsScalarTower ↥A₁ ↥K₁ T]
    (jT : T) [Fact (jT ≠ 0)] (htj : Transcendental ↥K₁ jT)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ↥K₁ ({jT} : Set T)) T)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₁ ({jT} : Set T)) T)
    (e : ↥K ≃+* T) (hcomm : ∀ a : ↥A₁, e (algebraMap ↥A₁ ↥K a) = algebraMap ↥A₁ T a)
    (hj : (((e.symm jT : ↥K)) : LaurentSeries ↥K₁) = coeffEmb ↥K₁ jq)
    (ψ : T →+* ↥E)
    (hψ : ∀ w : ↥K, ((ψ (e w) : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((w : ↥K) : LaurentSeries ↥K₁)) :
    (∀ g : Fbar, ∃ a b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ T jT),
      ∃ (ha : ψ (a : T) ∈ R.integers) (hb : ψ (b : T) ∈ R.integers),
        R.residue ⟨ψ (b : T), hb⟩ ≠ 0 ∧ g * R.residue ⟨ψ (b : T), hb⟩ = R.residue ⟨ψ (a : T), ha⟩) ∧
    (∀ g : Fbar, ∃ a b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ T jT),
      ∃ (ha : ψ (a : T) ∈ R.integers) (hb : ψ (b : T) ∈ R.integers),
        R.residue ⟨ψ (b : T), hb⟩ ≠ 0 ∧ g * R.residue ⟨ψ (b : T), hb⟩ = R.residue ⟨ψ (a : T), ha⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective.solution
