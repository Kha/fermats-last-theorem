import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_of_isReduced_of_perfectField

theorem Algebra.FormallyUnramified.of_isReduced_of_perfectField (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] : Algebra.FormallyUnramified K B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_of_isReduced_of_perfectField.solution
