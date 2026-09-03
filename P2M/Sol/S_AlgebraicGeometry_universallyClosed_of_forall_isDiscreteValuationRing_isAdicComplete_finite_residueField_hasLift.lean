import Mathlib
import Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
import Theorems.Thm_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {B : Type u} [CommRing B] [Algebra.FiniteType ℤ B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [LocallyOfFiniteType f]
    (H : ∀ (S : ValuativeCommSq f) [IsDiscreteValuationRing S.R] [IsAdicComplete (IsLocalRing.maximalIdeal S.R) S.R]
      [Finite (IsLocalRing.ResidueField S.R)], S.commSq.HasLift) :
    UniversallyClosed f := by
  apply AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
  intro S _ _
  obtain ⟨S', h1, h2, h3, h4⟩ :=
    AlgebraicGeometry.ValuativeCommSq.exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift f S
  haveI := h1; haveI := h2; haveI := h3
  exact h4 (H S')
