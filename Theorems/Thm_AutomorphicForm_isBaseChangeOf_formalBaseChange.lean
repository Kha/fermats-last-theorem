import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isBaseChangeOf_formalBaseChange

open IsDedekindDomain NumberField AutomorphicForm
theorem AutomorphicForm.isBaseChangeOf_formalBaseChange
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    {R : Type*} [CommRing R] (π : HeckeEigensystem F R) :
    IsBaseChangeOf π (formalBaseChange F K π) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isBaseChangeOf_formalBaseChange.solution
