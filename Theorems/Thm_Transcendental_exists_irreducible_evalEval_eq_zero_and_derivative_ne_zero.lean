import Mathlib
import P2M.Util
import P2M.Sol.S_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero

set_option autoImplicit false

open Polynomial

theorem Transcendental.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    {z : F} (hz : Transcendental K z) (y : F) :
    ∃ G : Polynomial (Polynomial K), Irreducible G ∧
      (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0 ∧
      ((Polynomial.derivative G).map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero.solution
