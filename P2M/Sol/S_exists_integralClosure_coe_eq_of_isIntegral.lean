import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import P2M.Util
namespace P2MW.S_exists_integralClosure_coe_eq_of_isIntegral

theorem solution {z : ℂ} (hz : IsIntegral ℤ z) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = z :=
  ⟨⟨z, (mem_integralClosure_iff ℤ ℂ).mpr hz⟩, rfl⟩
