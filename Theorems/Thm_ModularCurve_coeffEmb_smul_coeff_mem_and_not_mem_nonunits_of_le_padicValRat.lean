import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
    {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
    {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (g : LaurentSeries ℚ) (n : ℤ)
    (hle : ∀ k : ℤ, g.coeff k ≠ 0 → n ≤ padicValRat p (g.coeff k))
    (k₀ : ℤ) (hk₀ : g.coeff k₀ ≠ 0) (hk₀n : padicValRat p (g.coeff k₀) = n) :
    (∀ k : ℤ, (coeffEmb K (((p : ℚ) ^ n)⁻¹ • g)).coeff k ∈ A) ∧
      (coeffEmb K (((p : ℚ) ^ n)⁻¹ • g)).coeff k₀ ∉ A.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat.solution
