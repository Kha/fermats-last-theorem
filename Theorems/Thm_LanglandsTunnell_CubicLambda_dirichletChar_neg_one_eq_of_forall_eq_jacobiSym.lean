import Definitions.Def_LanglandsTunnell_CubicLambda
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicLambda_dirichletChar_neg_one_eq_of_forall_eq_jacobiSym

set_option autoImplicit false

theorem LanglandsTunnell.CubicLambda.dirichletChar_neg_one_eq_of_forall_eq_jacobiSym
    {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (d : ℤ) (M : ℕ) (hM : M ≠ 0)
    (hlaw : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ψ (ℓ : ZMod N) = (jacobiSym d ℓ : ℂ)) :
    ψ (-1) = if d < 0 then -1 else 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicLambda_dirichletChar_neg_one_eq_of_forall_eq_jacobiSym.solution
