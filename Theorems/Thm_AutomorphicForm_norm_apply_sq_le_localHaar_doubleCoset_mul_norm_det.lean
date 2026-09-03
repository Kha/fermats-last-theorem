import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ρ : GL (Fin 2) (v.adicCompletion K)) :
    1 ≤ AutomorphicForm.localHaar K v
        (AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v) ∧
    AutomorphicForm.localHaar K v
        (AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v) < ⊤ ∧
    ∀ g ∈ AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
        AutomorphicForm.localIntegralSet K v,
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ =
          ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ∧
      ∀ i j : Fin 2,
        ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ^ 2 ≤
          (AutomorphicForm.localHaar K v
              (AutomorphicForm.localIntegralSet K v * ({ρ} : Set (GL (Fin 2) (v.adicCompletion K))) *
                AutomorphicForm.localIntegralSet K v)).toReal *
            ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det.solution
