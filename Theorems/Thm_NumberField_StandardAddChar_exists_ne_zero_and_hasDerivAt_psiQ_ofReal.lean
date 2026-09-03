import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
NumberField.StandardAddChar.exists_ne_zero_and_hasDerivAt_psiQ_ofReal :
    ∃ lam : ℂ, lam ≠ 0 ∧
      HasDerivAt
        (fun s : ℝ => NumberField.StandardAddChar.psiQ
          ((AutomorphicForm.StandardKernel.ofReal s, 0) : AdeleRing (𝓞 ℚ) ℚ))
        lam 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal.solution
