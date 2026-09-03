import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
attribute [-instance] AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory
open scoped Classical in

theorem AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
    (K : Type) [Field K] [NumberField K]
    (U : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)) (hU : U ∈ nhds (archEntries K 1)) :
    ∃ (n : ℕ) (Ψ : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ),
      (∀ k, Continuous (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U ∧
        ∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K),
          Ψ k (Matrix.of.symm
              (Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ)) * Matrix.of E *
                Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ⁻¹)))) = Ψ k E) ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
        ∃ Φ' : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
          (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
          ∀ X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K,
            Φ X = ∑ k, ∫ E, Φ' k (Matrix.of.symm (Matrix.of X * Matrix.of E)) * Ψ k E := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries.solution
