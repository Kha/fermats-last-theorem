import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

theorem HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.solution
