import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq

set_option autoImplicit false

p2m_open "AlgebraicCurve AlgebraicCurve.Place~taylorCoeff_mul"

theorem AlgebraicCurve.Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {s : F} (hs : s ∈ v.toValuationSubring) (hs0 : v.evalAt s ≠ 0)
    (m : ℕ) (σ : ℕ → K)
    (hσ : ∀ r, r < m →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ x.1 * taylorCoeff v t x.2 s = if r = 0 then 1 else 0) :
    ∀ r, r < m → σ r = taylorCoeff v t r s⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq.solution
