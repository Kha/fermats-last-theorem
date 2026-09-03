import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Fin
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero

set_option autoImplicit false

open Polynomial

open scoped Polynomial.Bivariate
theorem ModularCurve.CharPModel.exists_monic_eval2_inv_mul_inv_pow_eq_zero {R K : Type*} [CommRing R] [Nontrivial R]
    [Field K] (f : R →+* K) (P : R[X][Y]) (hP : P.Monic) (m : ℕ)
    (hdeg : ∀ i < P.natDegree, (P.coeff i).natDegree ≤ m * (P.natDegree - i))
    {x : K} (hx : x ≠ 0) (y : K) (hroot : P.eval₂ (eval₂RingHom f x) y = 0) :
    ∃ Q : R[X][Y], Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.eval₂ (eval₂RingHom f x⁻¹) (y * x⁻¹ ^ m) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero.solution
