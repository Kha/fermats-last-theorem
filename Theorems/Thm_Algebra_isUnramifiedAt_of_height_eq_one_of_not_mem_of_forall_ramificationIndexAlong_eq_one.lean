import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one

set_option autoImplicit false

theorem Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (F : Type) [Field F] [Algebra L F] [Algebra A F] [IsScalarTower A L F]
    (F' : Type) [Field F'] [Algebra L F'] [Algebra A F'] [IsScalarTower A L F']
    (φ : F' →ₐ[L] F)
    (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Algebra B F] [IsScalarTower A B F]
    [IsFractionRing B F]
    (B' : Type) [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A B'] [Algebra B' F']
    [IsScalarTower A B' F'] [IsFractionRing B' F']
    [Algebra B' B] [IsScalarTower A B' B] [Module.Finite B' B]
    (hι : ∀ x : B', algebraMap B F (algebraMap B' B x) = φ (algebraMap B' F' x))
    (hint : φ.toRingHom.IsIntegral)
    (jB : B)
    (he : ∀ w : AlgebraicCurve.Place L F, 0 ≤ w.ord (algebraMap B F jB) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal B) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A B ϖ ∉ Q) :
    Algebra.IsUnramifiedAt B' Q := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one.solution
