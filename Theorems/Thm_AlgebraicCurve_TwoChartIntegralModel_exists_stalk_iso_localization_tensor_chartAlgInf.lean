import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_tensor_chartAlgInf

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_tensor_chartAlgInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (O : Type u) [CommRing O] [Algebra R O]
    (x : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))))
    (hx : x ∈ (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)) :
    ∃ (𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] O))
      (e : (pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime 𝔮.asIdeal)),
      (∀ o : O, e.hom ((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.germ ⊤ x trivial
          ((pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) =
        algebraMap (↥(chartAlgInf R F j) ⊗[R] O) (Localization.AtPrime 𝔮.asIdeal) (1 ⊗ₜ o)) ∧
      (∀ a : ↥(chartAlgInf R F j), e.hom ((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))).presheaf.germ ((pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)) x hx
          (((pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))).app ((ιInf R F j) ''ᵁ ⊤)) (((ιInf R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv a)))) =
        algebraMap (↥(chartAlgInf R F j) ⊗[R] O) (Localization.AtPrime 𝔮.asIdeal) (a ⊗ₜ 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_tensor_chartAlgInf.solution
