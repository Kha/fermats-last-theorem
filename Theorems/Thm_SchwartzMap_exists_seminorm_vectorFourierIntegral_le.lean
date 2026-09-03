import Mathlib
import P2M.Util
import P2M.Sol.S_SchwartzMap_exists_seminorm_vectorFourierIntegral_le

open scoped FourierTransform SchwartzMap
theorem SchwartzMap.exists_seminorm_vectorFourierIntegral_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(V, ℂ), ∃ g : 𝓢(V, ℂ),
      ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f ∧
      SchwartzMap.seminorm ℝ k n g ≤ C * (s.sup (schwartzSeminormFamily ℝ V ℂ)) f := by p2m_exact_reverting @_root_.P2MW.S_SchwartzMap_exists_seminorm_vectorFourierIntegral_le.solution
