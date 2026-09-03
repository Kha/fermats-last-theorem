import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_abv_eval_le_gaussNorm

set_option autoImplicit false

open Polynomial

theorem Polynomial.abv_eval_le_gaussNorm {R : Type*} [CommRing R] (v : AbsoluteValue R ℝ)
    (hv : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) (p : R[X]) {z : R} (hz : v z ≤ c) :
    v (p.eval z) ≤ p.gaussNorm v c := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_abv_eval_le_gaussNorm.solution
