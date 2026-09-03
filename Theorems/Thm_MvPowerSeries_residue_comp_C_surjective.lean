import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_residue_comp_C_surjective

universe u v w
theorem MvPowerSeries.residue_comp_C_surjective {σ : Type u} {R : Type v} [CommRing R] [IsLocalRing R] : Function.Surjective (⇑(IsLocalRing.residue (MvPowerSeries σ R)) ∘ ⇑(MvPowerSeries.C (σ := σ) (R := R))) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_residue_comp_C_surjective.solution
