import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one

universe v

theorem HopfAlgebra.convPow_natCard_algHom_algebraicClosure_eq_one
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (T : Type v) [CommRing T] (f : WithConv (K →ₐ[ℤ] T)) :
    f ^ Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one.solution
