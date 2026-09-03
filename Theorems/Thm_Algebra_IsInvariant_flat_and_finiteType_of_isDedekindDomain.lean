import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_flat_and_finiteType_of_isDedekindDomain

set_option autoImplicit false

theorem Algebra.IsInvariant.flat_and_finiteType_of_isDedekindDomain
    {B S A : Type*} [CommRing B] [IsDedekindDomain B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [Algebra.IsInvariant S A G]
    [Module.Flat B A] [Algebra.FiniteType B A] :
    Module.Flat B S ∧ Algebra.FiniteType B S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_flat_and_finiteType_of_isDedekindDomain.solution
