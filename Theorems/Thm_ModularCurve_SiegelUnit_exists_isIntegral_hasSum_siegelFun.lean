import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun (N : ℕ) (r s : ℤ)
    (hr : 0 ≤ r) (hrN : r < N) (hs : r = 0 → ¬ (N : ℤ) ∣ s) :
    ∃ c : ℕ → ℂ, (∀ n : ℕ, IsIntegral ℤ (c n)) ∧
      c 0 = (if r = 0 then 1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) / (N : ℂ)) else 1) ∧
      IsIntegral ℤ ((N : ℂ) * (c 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          (siegelFun N r s (τ : ℂ) /
            (-Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
              Complex.exp (2 * Real.pi * Complex.I *
                (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
                  (12 * (N : ℂ) ^ 2))))) ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ) /
            (-Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
              Complex.exp (2 * Real.pi * Complex.I *
                (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
                  (12 * (N : ℂ) ^ 2))))
        UpperHalfPlane.atImInfty (nhds (c 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.solution
