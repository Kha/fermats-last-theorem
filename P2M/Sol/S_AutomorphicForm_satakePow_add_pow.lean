import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import P2M.Util
namespace P2MW.S_AutomorphicForm_satakePow_add_pow

open IsDedekindDomain NumberField AutomorphicForm

theorem solution {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, AutomorphicForm.satakePow n (α + β) (α * β) = α ^ n + β ^ n := by
  have key : ∀ n : ℕ,
      AutomorphicForm.satakePow n (α + β) (α * β) = α ^ n + β ^ n ∧
      AutomorphicForm.satakePow (n + 1) (α + β) (α * β) = α ^ (n + 1) + β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · show (2 : R) = α ^ 0 + β ^ 0
        rw [pow_zero, pow_zero]; norm_num
      · show α + β = α ^ 1 + β ^ 1
        rw [pow_one, pow_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [AutomorphicForm.satakePow_add_two, ih.1, ih.2]; ring
  exact fun n => (key n).1
