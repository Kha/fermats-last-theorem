import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType

universe u v

theorem Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.solution
