import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (δ B : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
      ∃ α : ℂ, α ≠ 0 ∧
        ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ,
          (∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
          (∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
          ∀ J : v.adicCompletion K → ℂ,
            (∀ s : v.adicCompletion K, J s = ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
              Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)) →
            J t = J 0 + α * Φ 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare.solution
