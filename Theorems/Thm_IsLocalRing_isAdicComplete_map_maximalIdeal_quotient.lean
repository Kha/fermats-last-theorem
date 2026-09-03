import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient

universe u v w
theorem IsLocalRing.isAdicComplete_map_maximalIdeal_quotient {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (J : Ideal R) : IsAdicComplete ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)) (R ⧸ J) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient.solution
