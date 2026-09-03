import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) (he : e 0 0 = 0) :
    ∃ (C : ℂ) (d : ℕ → ℂ), C ^ N = 1 ∧ (∀ n : ℕ, IsIntegral ℤ (d n)) ∧
      d 0 = ∏ s : ZMod N,
        (1 - Complex.exp (2 * Real.pi * Complex.I * (s.val : ℂ) / (N : ℂ))) ^ (12 * N * e 0 s) ∧
      d 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, e r s) * (d 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => d n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          ((∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))) ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane =>
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))
        UpperHalfPlane.atImInfty (nhds (d 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.solution
