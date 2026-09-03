import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_isDiscreteValuationRing_ratLocalizedAt

theorem GaloisRep.isDiscreteValuationRing_ratLocalizedAt (p : ℕ) (hp : p.Prime) :
    IsDiscreteValuationRing (GaloisRep.ratLocalizedAt p) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isDiscreteValuationRing_ratLocalizedAt.solution
