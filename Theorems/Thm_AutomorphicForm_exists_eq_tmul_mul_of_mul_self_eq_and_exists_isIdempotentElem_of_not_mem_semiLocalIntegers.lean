import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ϖ : K) (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) :
    (∀ x ∈ AutomorphicForm.semiLocalIntegers K L v, ∀ y ∈ AutomorphicForm.semiLocalIntegers K L v,
        x * x = ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * y →
        ∃ z ∈ AutomorphicForm.semiLocalIntegers K L v,
          x = ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * z) ∧
    (∀ x : L ⊗[K] v.adicCompletion K, x ∉ AutomorphicForm.semiLocalIntegers K L v →
        ∃ y ∈ AutomorphicForm.semiLocalIntegers K L v, ∃ e ∈ AutomorphicForm.semiLocalIntegers K L v,
          e ≠ 0 ∧ IsIdempotentElem e ∧
            ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * x * y = e) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers.solution
