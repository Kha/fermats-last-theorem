import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed

universe u v w

theorem Algebra.isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed
    (k : Type u) [Field k] [PerfectField k]
    (K : Type v) [Field K] [Algebra k K] [IsAlgClosed K]
    (A : Type w) [CommRing A] [Algebra k A] [Module.Finite k A] :
    IsReduced A ↔ Nat.card (A →ₐ[k] K) = Module.finrank k A := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed.solution
