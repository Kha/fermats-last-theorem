import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import P2M.Util
import P2M.Sol.S_ValuationSubring_residueValuationSubring_valuation_lt_one_iff

theorem ValuationSubring.residueValuationSubring_valuation_lt_one_iff
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) (a : A) :
    (A.residueValuationSubring S h).valuation (IsLocalRing.residue S (A.inclusion S h a)) < 1 ↔
      A.valuation (a : L) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_residueValuationSubring_valuation_lt_one_iff.solution
