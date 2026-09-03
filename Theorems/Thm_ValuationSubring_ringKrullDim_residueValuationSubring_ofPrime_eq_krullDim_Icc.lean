import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import P2M.Util
import P2M.Sol.S_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc

theorem ValuationSubring.ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc
    {L : Type*} [Field L] (A : ValuationSubring L) (Q P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (hQP : Q ≤ P) :
    ringKrullDim ((A.ofPrime P).residueValuationSubring (A.ofPrime Q)
        (ValuationSubring.ofPrime_le_of_le A Q P hQP)) =
      Order.krullDim (Set.Icc (⟨Q, inferInstance⟩ : PrimeSpectrum A) ⟨P, inferInstance⟩) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc.solution
