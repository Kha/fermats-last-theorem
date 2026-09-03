import Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Arcosh
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing

set_option autoImplicit false

open AutomorphicForm.GL2Twisted Polynomial

theorem
AutomorphicForm.GL2Twisted.ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing
    (k : ℕ) (hk : 2 ≤ k) (r T : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
          (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing.solution
