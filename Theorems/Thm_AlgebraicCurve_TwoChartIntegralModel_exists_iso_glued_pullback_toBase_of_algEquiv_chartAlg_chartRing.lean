import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

set_option maxHeartbeats 800000 in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (K : Type u) [Field K] [Algebra R K]
    {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (eFin : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃ₐ[K] ↥(CurveModel.chartRing K ({t} : Set L)))
    (eInf : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgInf R F j) ≃ₐ[K] ↥(CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t)
    (hjInv : ((eInf ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jInvChartInf R F j)) : L) = t⁻¹)
    (hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) (b' : ↥(TwoChartIntegralModel.chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((eFin ((1 : K) ⊗ₜ[R] b)) : L) = ((eInf ((1 : K) ⊗ₜ[R] b')) : L) * t ^ n) :
    ∃ (es : CurveModel.glued K t ⟶ pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (_ : IsIso es),
      es ≫ pullback.snd (TwoChartIntegralModel.toBase R F j) _ = CurveModel.gluedToBase K t ∧
      (CurveModel.ι₀ K t ≫ es ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j))).toRingHom)) ≫
          TwoChartIntegralModel.ιFin R F j) ∧
      (CurveModel.ιInf K t ≫ es ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgInf R F j))).toRingHom)) ≫
          TwoChartIntegralModel.ιInf R F j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing.solution
