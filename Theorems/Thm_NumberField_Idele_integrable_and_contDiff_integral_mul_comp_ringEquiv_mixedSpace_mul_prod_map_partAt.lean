import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hξc : Continuous ξ)
    (G : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (hG0 : ∀ (x : mixedEmbedding.mixedSpace K) (y : InfiniteAdeleRing K),
      G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K y) ≠ 0 → y ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)
    (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) :
    (∀ x : mixedEmbedding.mixedSpace K,
      Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ξ zS *
          (G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))
        (Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace K =>
      ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ξ zS *
          (G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
        ∂(Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt.solution
