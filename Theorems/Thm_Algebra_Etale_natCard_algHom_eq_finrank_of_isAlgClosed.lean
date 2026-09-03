import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed

theorem Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R] [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.solution
