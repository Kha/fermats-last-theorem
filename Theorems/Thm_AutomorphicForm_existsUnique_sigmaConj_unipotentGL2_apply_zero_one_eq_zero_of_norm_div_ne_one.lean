import Definitions.Def_AutomorphicForm_SigmaConjugacy
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one

set_option autoImplicit false

theorem AutomorphicForm.existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (σ : L ≃ₐ[F] L) (γ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hN : Algebra.norm F ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    ∃! s : L, ((AutomorphicForm.sigmaConj (σ : L →+* L) (AutomorphicForm.unipotentGL2 s) γ :
        Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one.solution
