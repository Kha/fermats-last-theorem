import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
namespace P2MW.S_AutomorphicForm_isBaseChangeOf_formalBaseChange

open IsDedekindDomain NumberField AutomorphicForm

theorem solution
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)]
    [Algebra.IsIntegral (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)]
    {R : Type*} [CommRing R] (π : AutomorphicForm.HeckeEigensystem F R) :
    AutomorphicForm.IsBaseChangeOf π (AutomorphicForm.formalBaseChange F K π) :=
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩
