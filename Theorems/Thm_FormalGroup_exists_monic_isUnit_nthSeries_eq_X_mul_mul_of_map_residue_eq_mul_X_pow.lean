import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (q : ℕ) [Fact q.Prime] (F : FormalGroup S)
    (hF : ∃ u : PowerSeries (ResidueField S), IsUnit u ∧
      PowerSeries.map (residue S) (F.nthSeries q) = u * PowerSeries.X ^ q) :
    ∃ (g : S[X]) (v : PowerSeries S), g.Monic ∧ g.natDegree = q - 1 ∧
      (∀ i < q - 1, g.coeff i ∈ maximalIdeal S) ∧
      (∃ w : S, IsUnit w ∧ g.coeff 0 = (q : S) * w) ∧ IsUnit v ∧
      F.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow.solution
