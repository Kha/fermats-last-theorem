import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart
    (p : ℕ) {Γ Γ' : Subgroup SL(2, ℤ)} (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    (ψ : ↥(chartAlgFin p Γ' hj) →ₐ[R p] ↥(chartAlgFin p Γ hj))
    (hφchart : ιFin p Γ hj ≫ φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιFin p Γ' hj)
    (κ : Type) [CommRing κ] [Algebra (R p) κ]
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom) ≫ ιFin p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj)))))
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ' hj))) ⟶ fibre (Γ := Γ') (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))).toRingHom) ≫ ιFin p Γ' hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))))) :
    c ≫ fibreMap φ (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) ψ).toRingHom) ≫ c' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart.solution
