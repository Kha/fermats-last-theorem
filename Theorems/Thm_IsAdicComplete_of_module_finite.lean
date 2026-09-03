import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_IsAdicComplete_of_module_finite

universe u v w
theorem IsAdicComplete.of_module_finite {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_of_module_finite.solution
