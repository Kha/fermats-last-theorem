import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.IsFiniteOrderHeckeChar.exists_admitsModulus
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ N : ℕ, N ≠ 0 ∧ HeckeCharacter.AdmitsModulus ℚ μ (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus.solution
