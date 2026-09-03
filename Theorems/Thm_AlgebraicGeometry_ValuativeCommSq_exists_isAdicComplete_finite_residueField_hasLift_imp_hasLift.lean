import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ValuativeCommSq.exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
    {X Y : Scheme.{u}} (f : X ⟶ Y) (S : ValuativeCommSq f)
    [IsDiscreteValuationRing S.R] [Finite (IsLocalRing.ResidueField S.R)] :
    ∃ S' : ValuativeCommSq f, IsDiscreteValuationRing S'.R ∧ IsAdicComplete (IsLocalRing.maximalIdeal S'.R) S'.R ∧
      Finite (IsLocalRing.ResidueField S'.R) ∧ (S'.commSq.HasLift → S.commSq.HasLift) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift.solution
