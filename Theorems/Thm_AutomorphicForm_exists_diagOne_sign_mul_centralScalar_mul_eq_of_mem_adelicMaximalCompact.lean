import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F]
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ AutomorphicForm.adelicMaximalCompact F) :
    ∃ (a z : (AdeleRing (𝓞 F) F)ˣ) (k₁ : AdelicGL2 (𝓞 F) F),
      ((a : AdeleRing (𝓞 F) F).2 = 1 ∧
        ∀ w : InfinitePlace F, (a : AdeleRing (𝓞 F) F).1 w = 1 ∨ (a : AdeleRing (𝓞 F) F).1 w = -1) ∧
      AutomorphicForm.centralScalar (𝓞 F) F z ∈ AutomorphicForm.adelicMaximalCompact F ∧
      k₁ ∈ AutomorphicForm.adelicMaximalCompact F ∧
      (∀ w : InfinitePlace F,
        ((archComponent F w (glArch (𝓞 F) F k₁) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) ∧
      k = NumberField.AdelicLevel.diagOne a * AutomorphicForm.centralScalar (𝓞 F) F z * k₁ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact.solution
