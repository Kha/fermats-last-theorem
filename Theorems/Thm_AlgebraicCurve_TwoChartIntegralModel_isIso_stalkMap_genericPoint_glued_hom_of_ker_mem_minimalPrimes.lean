import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes
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
          y ∈ Set.range (CurveModel.ι₀ κ t).base)
    (hmin : RingHom.ker (θFin.toRingHom.comp
        (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) ∈
      minimalPrimes (↥(chartAlgFin R F j) ⊗[R] κ))
    (hred : _root_.IsReduced ((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.stalk
      (c.base (genericPoint (CurveModel.glued κ t)))))
    (hfrac : ∀ x : L, ∃ a b : κ ⊗[R] ↥(chartAlgFin R F j),
      ((θFin b : ↥(CurveModel.chartRing κ ({t} : Set L))) : L) ≠ 0 ∧
        x * ((θFin b : ↥(CurveModel.chartRing κ ({t} : Set L))) : L) = ((θFin a : ↥(CurveModel.chartRing κ ({t} : Set L))) : L)) :
    IsIso (c.stalkMap (genericPoint (CurveModel.glued κ t))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes.solution
