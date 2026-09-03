import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isUnit_withConv_algHom

theorem HopfAlgebra.isUnit_withConv_algHom
    {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]
    {L : Type*} [CommSemiring L] [Algebra R L]
    (φ : WithConv (A →ₐ[R] L)) : IsUnit φ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isUnit_withConv_algHom.solution
