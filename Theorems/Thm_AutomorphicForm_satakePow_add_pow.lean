import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import P2M.Util
import P2M.Sol.S_AutomorphicForm_satakePow_add_pow

open IsDedekindDomain NumberField AutomorphicForm
theorem AutomorphicForm.satakePow_add_pow {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, satakePow n (α + β) (α * β) = α ^ n + β ^ n := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_satakePow_add_pow.solution
