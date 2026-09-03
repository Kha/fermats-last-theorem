import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ) :
    let ε : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by simp)
    HasArchCharacterAt₀ F w (archWeightCharAt hw (-k)) (fun g => φ (g * archRealGLAt hw ε)) ∧
    (IsArchSmoothAt hw φ → IsArchSmoothAt hw (fun g => φ (g * archRealGLAt hw ε))) ∧
    (archCasimirAt hw (fun g => φ (g * archRealGLAt hw ε)) =
      fun g => archCasimirAt hw φ (g * archRealGLAt hw ε)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one.solution
