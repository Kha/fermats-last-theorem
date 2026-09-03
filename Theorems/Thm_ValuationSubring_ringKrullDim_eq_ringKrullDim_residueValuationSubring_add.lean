import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import P2M.Util
import P2M.Sol.S_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add

theorem ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.solution
