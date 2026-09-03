import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ ≤ 1) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![π ^ m₁, π ^ m₂])
    (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
        AutomorphicForm.localIntegralSet K v ↔
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = ‖π‖ ^ (m₁ + m₂) ∧
      (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ ‖π‖ ^ m₂) ∧
      ∃ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ = ‖π‖ ^ m₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm.solution
