import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq_of_admitsModulus
import P2M.Util
namespace P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.dirichletIdeleChar = μ := by
  obtain ⟨N, hN0, hmod⟩ := hμ.exists_admitsModulus
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨χ, hχ⟩ := hμ.exists_dirichletIdeleChar_eq_of_admitsModulus hmod
  exact ⟨N, inferInstance, χ, hχ⟩
