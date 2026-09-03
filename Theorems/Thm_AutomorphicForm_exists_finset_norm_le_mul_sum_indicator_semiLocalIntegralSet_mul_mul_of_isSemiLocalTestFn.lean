import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ s : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        ‖φv g‖ ≤ M * ∑ a ∈ s,
          (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
            (fun _ => (1 : ℝ)) g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn.solution
