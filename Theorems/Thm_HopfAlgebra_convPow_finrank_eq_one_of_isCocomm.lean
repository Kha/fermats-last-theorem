import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm

universe u v w

theorem HopfAlgebra.convPow_finrank_eq_one_of_isCocomm
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ Module.finrank R H = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm.solution
