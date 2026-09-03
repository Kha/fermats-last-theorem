import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_pullback_snd_toBase_of_tensor_charts

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_pullback_snd_toBase_of_tensor_charts
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (k : Type u) [CommRing k] [Algebra R k] (n : ℕ)
    (hFin : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R] ↥(chartAlgFin R F j))))))
    (hInf : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R] ↥(chartAlgInf R F j)))))) :
    SmoothOfRelativeDimension n
      (pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_pullback_snd_toBase_of_tensor_charts.solution
