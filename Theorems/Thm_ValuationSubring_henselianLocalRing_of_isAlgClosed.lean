import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_henselianLocalRing_of_isAlgClosed

theorem ValuationSubring.henselianLocalRing_of_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) : HenselianLocalRing A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_henselianLocalRing_of_isAlgClosed.solution
