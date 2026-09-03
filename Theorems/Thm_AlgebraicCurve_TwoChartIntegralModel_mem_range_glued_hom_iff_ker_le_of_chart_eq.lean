import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_glued_hom_iff_ker_le_of_chart_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.mem_range_glued_hom_iff_ker_le_of_chart_eq
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)
    (hcFin : CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫
          ιFin R F j)
    (hcInf : CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
          ιInf R F j)
    (hmatch : ∀ y : ↥(CurveModel.glued κ t),
        (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔
          y ∈ Set.range (CurveModel.ι₀ κ t).base) :
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
                pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom.base z).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_glued_hom_iff_ker_le_of_chart_eq.solution
