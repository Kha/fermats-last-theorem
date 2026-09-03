import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal

set_option autoImplicit false

theorem MvPowerSeries.exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ g : B, g ∉ 𝔪 ∧ ∀ (R' : Type) [CommRing R'] [Algebra B R'], IsUnit (algebraMap B R' g) →
      Module.Free R' (MvPowerSeries (Fin 2) R' ⧸ I.map (MvPowerSeries.map (algebraMap B R'))) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal.solution
