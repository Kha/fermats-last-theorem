import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import P2M.Util
import P2M.Sol.S_AutomorphicForm_finite_preimage_satakePow_pow

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.finite_preimage_satakePow_pow {R : Type*} [CommRing R] [IsDomain R]
    (f : ℕ) (hf : f ≠ 0) (c : R × R) :
    ((fun p : R × R => (satakePow f p.1 p.2, p.2 ^ f)) ⁻¹' {c}).Finite := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_finite_preimage_satakePow_pow.solution
