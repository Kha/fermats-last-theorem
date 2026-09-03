import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_IsLocalRing_isAdicComplete_of_module_finite

universe u v w
theorem IsLocalRing.isAdicComplete_of_module_finite {𝒪 : Type u} {T : Type v} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T] [IsLocalHom (algebraMap 𝒪 T)] : IsAdicComplete (IsLocalRing.maximalIdeal T) T := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isAdicComplete_of_module_finite.solution
