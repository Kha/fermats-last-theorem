import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq

theorem MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
    {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n₁ n₂ : ℕ} (e : Fin n₁ → V) (f : Fin n₂ → V)
    (he : LinearIndependent ℝ e) (hf : LinearIndependent ℝ f)
    (hspan : Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range f)) :
    ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e i) (e j)).det|)) •
        Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e i) volume)
      ((fun a : Fin n₂ → ℝ => ∑ i, a i • f i) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) =
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (f i) (f j)).det|) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq.solution
