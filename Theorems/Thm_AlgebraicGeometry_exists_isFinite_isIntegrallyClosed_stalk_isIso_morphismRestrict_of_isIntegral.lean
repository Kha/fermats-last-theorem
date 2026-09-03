import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
    (k : Type u) [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))
    [IsIntegral Y] [LocallyOfFiniteType q] :
    ∃ (Y' : Scheme.{u}) (ν : Y' ⟶ Y), IsIntegral Y' ∧
      (∀ z : Y', IsIntegrallyClosed (Y'.presheaf.stalk z)) ∧ IsFinite ν ∧
      Function.Surjective ν.base ∧
      (∀ z : Y', ringKrullDim (Y'.presheaf.stalk z) =
        ringKrullDim (Y.presheaf.stalk (ν.base z))) ∧
      ∀ U : Y.Opens, (∀ z ∈ U, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsIso (ν ∣_ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral.solution
