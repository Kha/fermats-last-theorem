import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_DirichletCharacter_admitsModulus_dirichletIdeleChar

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem DirichletCharacter.admitsModulus_dirichletIdeleChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    HeckeCharacter.AdmitsModulus ℚ χ.dirichletIdeleChar (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) := by p2m_exact_reverting @_root_.P2MW.S_DirichletCharacter_admitsModulus_dirichletIdeleChar.solution
