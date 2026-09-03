import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_glued_pullback_of_surjective
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hFin : Function.Surjective θFin) (hInf : Function.Surjective θInf)
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((θFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((θInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n)) :
    ∃ c : CurveModel.glued κ t ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      IsClosedImmersion c ∧
      c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t ∧
      (CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫
          ιFin R F j) ∧
      (CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
          ιInf R F j) ∧

      (∀ y : ↥(CurveModel.glued κ t),
        (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔
          y ∈ Set.range (CurveModel.ι₀ κ t).base) ∧

      (∀ z : ↥(pullback (ιFin R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιFin R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θFin.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιFin R F j) ≪≫
                pullback.congrHom (ιFin_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom.base z).asIdeal) ∧
      (∀ z : ↥(pullback (ιInf R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιInf R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θInf.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιInf R F j) ≪≫
                pullback.congrHom (ιInf_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom.base z).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective.solution
