import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid

open scoped NumberField
theorem IsCyclotomicExtension.Rat.seven_pid (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution
