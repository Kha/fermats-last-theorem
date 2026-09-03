import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero

universe u v w
theorem HopfAlgebra.natCard_algHom_eq_finrank_of_charZero (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Free R H]
    (K : Type w) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] :
    Nat.card (H →ₐ[R] K) = Module.finrank R H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero.solution
