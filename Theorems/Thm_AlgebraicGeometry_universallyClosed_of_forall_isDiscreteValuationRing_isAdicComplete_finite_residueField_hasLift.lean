import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift

universe u

theorem AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift
    {B : Type u} [CommRing B] [Algebra.FiniteType ℤ B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [LocallyOfFiniteType f]
    (H : ∀ (S : ValuativeCommSq f) [IsDiscreteValuationRing S.R] [IsAdicComplete (IsLocalRing.maximalIdeal S.R) S.R]
      [Finite (IsLocalRing.ResidueField S.R)], S.commSq.HasLift) :
    UniversallyClosed f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift.solution
