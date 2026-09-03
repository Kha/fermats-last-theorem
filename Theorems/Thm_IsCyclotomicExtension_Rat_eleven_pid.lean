import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_Rat_eleven_pid

open scoped NumberField
theorem IsCyclotomicExtension.Rat.eleven_pid (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_eleven_pid.solution
