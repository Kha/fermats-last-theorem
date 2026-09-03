import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
attribute [-instance] AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : IsArchKFinite F φ) (_hφf : IsKfSmooth F φ) (_hφc : Continuous φ) :
    ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (a : Fin m → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, (∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → AdelicGL2 (𝓞 F) F),
          (∀ i, glFin (𝓞 F) F (k i) ∈ finiteIntegralGL2 (𝓞 F) F ∧
            ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (k i)))) ∧
          e j = fun x => ∑ i, c i * φ (x * k i)) ∧
        IsArchKFinite F (e j) ∧ IsKfSmooth F (e j)) ∧
      (∀ j, ContinuousOn (a j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ∀ x : AdelicGL2 (𝓞 F) F, φ (x * k) = ∑ j, a j k * e j x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth.solution
