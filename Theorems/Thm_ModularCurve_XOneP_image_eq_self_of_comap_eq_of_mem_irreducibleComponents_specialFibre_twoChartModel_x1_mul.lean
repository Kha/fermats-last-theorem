import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (σ : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hσ : σ.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (ρ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hsq : Spec.map (CommRingCat.ofHom ρ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j = ModularCurve.TwoChart.ιFin A (↥K) j ≫ σ.hom)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k]
    (hgen : ∀ (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))),
      hZ.1.genericPoint ∈ (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⁻¹ᵁ ModularCurve.TwoChart.chartFinOpen A (↥K) j :
        (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).Opens))
    (hfix : ∀ (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
      (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ.1.genericPoint →
        y.asIdeal.comap ρ = y.asIdeal)
    (hinj : ∀ (Z₁ Z₂ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (hZ₂ : Z₂ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
      (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₁.1.genericPoint →
      (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₂.1.genericPoint → Z₁ = Z₂) :
    ∀ Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      (curveChange σ.hom hσ (specMap A k)).base '' Z = Z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_image_eq_self_of_comap_eq_of_mem_irreducibleComponents_specialFibre_twoChartModel_x1_mul.solution
