import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.dirichletIdeleChar = μ := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq.solution
