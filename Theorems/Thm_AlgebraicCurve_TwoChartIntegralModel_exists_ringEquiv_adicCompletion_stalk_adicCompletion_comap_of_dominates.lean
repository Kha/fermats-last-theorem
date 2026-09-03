import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin R F j))
    (hz : (ιFin R F j).base y ∈ (ιFin R F j) ''ᵁ ⊤)
    (B : Type u) [CommRing B] (κ : B →+* ↥(chartAlgFin R F j)) (hκ : Function.Injective κ)
    (hdom : ∀ c : ↥(chartAlgFin R F j), ∃ b d : B, κ d ∉ y.asIdeal ∧ c * κ d = κ b)
    (hmax : (y.asIdeal.comap κ).IsMaximal) :
    let STK := (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)
    let germY : ↥(chartAlgFin R F j) →+* STK :=
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) hz).hom).comp
        (((((ιFin R F j).appIso ⊤).inv).hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom)
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal STK) STK ≃+* AdicCompletion (y.asIdeal.comap κ) B,
      ∀ b : B, e (algebraMap STK (AdicCompletion (IsLocalRing.maximalIdeal STK) STK) (germY (κ b))) =
        algebraMap B (AdicCompletion (y.asIdeal.comap κ) B) b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_dominates.solution
