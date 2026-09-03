import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SiegelFunction
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
    (q : ℕ) [Fact q.Prime] (μ : ZMod q → ℕ) (hμ0 : μ 0 = 0) (t : ℕ)
    (ht : ∀ x : ZMod q, x ≠ 0 →
      0 ≤ (∑ r : ZMod q, (μ r : ℤ) *
          (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ)) :
    ∃ ϑ : ModularForm (CongruenceSubgroup.Gamma1 q : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod q, ∏ s : ZMod q,
          ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
          ModularForm.discriminant τ ^ t) ∧
      ∃ (p : PowerSeries ℤ) (n₀ : ℕ), ModularCurve.IsIntegralQExp ϑ p ∧
        (n₀ : ℤ) = (∑ r : ZMod q, (μ r : ℤ) *
          (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) ∧
        (∀ n : ℕ, n < n₀ → PowerSeries.coeff n p = 0) ∧ PowerSeries.coeff n₀ p = 1 ∧
        ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
          ((UpperHalfPlane.qExpansion (q : ℝ) ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.solution
