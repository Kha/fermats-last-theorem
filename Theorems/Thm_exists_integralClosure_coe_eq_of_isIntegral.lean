import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import P2M.Util
import P2M.Sol.S_exists_integralClosure_coe_eq_of_isIntegral

theorem exists_integralClosure_coe_eq_of_isIntegral {z : ℂ} (hz : IsIntegral ℤ z) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = z := by p2m_exact_reverting @_root_.P2MW.S_exists_integralClosure_coe_eq_of_isIntegral.solution
