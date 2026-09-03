import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq
    {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (B : LinearMap.BilinForm ℝ V) {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V)
    (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n' => B (e' i) (e' j)).det|)) •
        Measure.map (fun c : Fin n' → ℝ => ∑ i, c i • e' i) volume =
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n => B (e i) (e j)).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq.solution
