import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible

theorem IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = GaloisRep.ratLocalizedAt p := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible.solution
