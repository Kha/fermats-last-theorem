import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_ModularCurve_LevelFunctionField
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
    (q : ℕ) [Fact q.Prime] (a : Fin 2 → ZMod q)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    HasSum
      (fun n : ℕ => ι (PowerSeries.coeff n (siegelSeries q a ^ (12 * q))) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (q : ℂ)))
      (siegelFun q ((a 0).val : ℤ) ((a 1).val : ℤ) (τ : ℂ) ^ (12 * q) /
        (ι (zetaQ q ^ siegelConstExponent q a) *
          Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q a : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.solution
