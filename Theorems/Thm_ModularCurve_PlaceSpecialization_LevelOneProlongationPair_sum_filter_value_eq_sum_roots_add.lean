import Mathlib
import Definitions.Def_ModularCurve_GaussPencilAdapter
import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree
attribute [-simp] ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open Classical in
theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
    [Algebra K₁ (modularFunctionFieldBar (1 * q))]
    [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]
    (R : P.LevelOneProlongationPair) [R.HasGaussTransport K₁]
    [FiniteDimensional K₁ (modularFunctionFieldBar (1 * q))] [Algebra.IsSeparable K₁ (modularFunctionFieldBar (1 * q))]
    [CharZero K₁] [DecidableEq k]
    (y f : modularFunctionFieldBar (1 * q))
    (hy₁ : y ∈ R.R₁.integers) (hf₁ : f ∈ R.R₁.integers) (hy₂ : y ∈ R.R₂.integers) (hf₂ : f ∈ R.R₂.integers)
    (hyint : IsIntegral (R.gaussBase K₁) y) (hfint : IsIntegral (R.gaussBase K₁) f)
    (hjS : PlaceSpecialization.jFun (q := q) ∈ R.gaussOrder K₁ y f) (hjqS : PlaceSpecialization.jqFun (q := q) ∈ R.gaussOrder K₁ y f)
    (hspan : Submodule.span K₁ (R.gaussOrder K₁ y f : Set (modularFunctionFieldBar (1 * q))) = ⊤)
    (hdeg : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne + Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo
      = Module.finrank K₁ (modularFunctionFieldBar (1 * q)))
    (hgen₁ : ∃ s : R.gaussOrder K₁ y f, ((LevelOneProlongationPair.ResOne.val R (R.rho₁ K₁ hy₁ hf₁ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (hgen₂ : ∃ s : R.gaussOrder K₁ y f, ((LevelOneProlongationPair.ResTwo.val R (R.rho₂ K₁ hy₂ hf₂ s) :
      modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A))
    (e₁ : RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] K₁) (hxV : e₁ RatFunc.X ∈ R.gaussBase K₁)
    (htr : Transcendental (ResidueField A) (IsLocalRing.residue (R.gaussBase K₁) ⟨e₁ RatFunc.X, hxV⟩))
    (r₁ r₂ : k[X]) (hr₁ : 0 < r₁.natDegree) (hr₂ : 0 < r₂.natDegree)
    (hres₁ : R.residue₁ ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X), (R.mem_gaussBase_iff _).mp hxV⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₁))
    (hres₂ : R.residue₂ ⟨algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X),
        R.algebraMap_mem_integers₂_of_mem_gaussBase _ hxV⟩
      = ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) r₂))
    (hdim₁ : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResOne = r₁.natDegree)
    (hdim₂ : Module.finrank (ResidueField (R.gaussBase K₁)) R.ResTwo = r₂.natDegree)
    (hu₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, hf₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (algebraMap K₁ (modularFunctionFieldBar (1 * q)) (e₁ RatFunc.X)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = (∑ a ∈ (r₁ - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, hf₁⟩))
        + ∑ b ∈ (r₂ - C c₀).roots.toFinset, (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, hf₂⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_sum_roots_add.solution
