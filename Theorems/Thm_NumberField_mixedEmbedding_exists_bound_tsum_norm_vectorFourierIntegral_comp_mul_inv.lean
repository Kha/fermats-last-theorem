import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv

open scoped FourierTransform SchwartzMap NumberField Classical
theorem NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (g : 𝓢(NumberField.mixedEmbedding.mixedSpace K, ℂ))
        (a : (NumberField.mixedEmbedding.mixedSpace K)ˣ),
        1 ≤ NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K) →
          Summable (fun ξ : 𝓞 K ↦ ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K))
              (fun x ↦ g (↑a⁻¹ * x)) (NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K))
              (fun x ↦ g (↑a⁻¹ * x)) (NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖
            ≤ C * (s.sup (schwartzSeminormFamily ℝ (NumberField.mixedEmbedding.mixedSpace K) ℂ)) g *
                (NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K))⁻¹ ^ N := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv.solution
