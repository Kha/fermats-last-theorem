import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (g : LaurentSeries ℚ) (hg : g ≠ 0) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (hcA : ∀ k : ℤ, c * (coeffEmb (AlgebraicClosure ℚ) g).coeff k ∈ A) :
    ∃ n : ℤ, (∀ k : ℤ, g.coeff k ≠ 0 → n ≤ padicValRat p (g.coeff k)) ∧
      ∃ k₀ : ℤ, g.coeff k₀ ≠ 0 ∧ padicValRat p (g.coeff k₀) = n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem.solution
