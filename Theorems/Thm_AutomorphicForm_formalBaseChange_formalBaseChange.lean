import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_AutomorphicForm_formalBaseChange_formalBaseChange

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.formalBaseChange_formalBaseChange
    (F K M : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    [Algebra (𝓞 K) (𝓞 M)] [Algebra.IsIntegral (𝓞 K) (𝓞 M)]
    [Algebra (𝓞 F) (𝓞 M)] [Algebra.IsIntegral (𝓞 F) (𝓞 M)]
    [IsScalarTower (𝓞 F) (𝓞 K) (𝓞 M)]
    {R : Type*} [CommRing R] (π : HeckeEigensystem F R) :
    formalBaseChange K M (formalBaseChange F K π) = formalBaseChange F M π := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_formalBaseChange_formalBaseChange.solution
