import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : HeckeCharacter.IsFiniteOrderHeckeChar ℚ χ.dirichletIdeleChar := by p2m_exact_reverting @_root_.P2MW.S_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar.solution
