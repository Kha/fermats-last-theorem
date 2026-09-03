import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_IsAdicComplete_map_of_surjective

universe u v w
theorem IsAdicComplete.map_of_surjective {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (f : R →+* S) (hf : Function.Surjective f) : IsAdicComplete (I.map f) S := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_map_of_surjective.solution
