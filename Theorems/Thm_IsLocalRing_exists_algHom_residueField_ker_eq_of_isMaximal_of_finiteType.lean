import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType
    {A : Type u} [CommRing A] [IsLocalRing A] [IsAlgClosed (ResidueField A)]
    {C : Type v} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (y : Ideal C) [y.IsMaximal] (hy : (maximalIdeal A).map (algebraMap A C) ≤ y) :
    ∃ ψ : C →ₐ[A] ResidueField A, RingHom.ker ψ.toRingHom = y := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType.solution
