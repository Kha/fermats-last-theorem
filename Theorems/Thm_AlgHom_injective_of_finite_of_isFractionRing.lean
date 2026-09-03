import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_injective_of_finite_of_isFractionRing

universe u
theorem AlgHom.injective_of_finite_of_isFractionRing {k A B K : Type u} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [Algebra k K] [Algebra A K] [IsFractionRing A K] [IsScalarTower k A K]
    [Algebra B K] [IsFractionRing B K] [IsScalarTower k B K]
    (φ : A →ₐ[k] B) (hφ : φ.toRingHom.Finite) : Function.Injective φ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_injective_of_finite_of_isFractionRing.solution
