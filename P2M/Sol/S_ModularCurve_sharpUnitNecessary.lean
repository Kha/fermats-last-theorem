import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_prime
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_one
import P2M.Util
namespace P2MW.S_ModularCurve_sharpUnitNecessary

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.SharpUnitNecessary ℓ := by
  by_cases h : ℓ % 12 = 1
  · exact ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one ℓ h
  · exact ModularCurve.sharpUnitNecessary_of_prime ℓ h
