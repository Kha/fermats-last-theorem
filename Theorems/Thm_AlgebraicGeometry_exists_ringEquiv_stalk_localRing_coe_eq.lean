import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_stalk_localRing_coe_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve

theorem AlgebraicGeometry.exists_ringEquiv_stalk_localRing_coe_eq
    (X : Scheme.{0}) [IsIntegral X] {F : Type} [Field F] (φ : F ≃+* X.functionField) (x : X) :
    ∃ e : X.presheaf.stalk x ≃+* ↥(SemistableModel.localRing X φ x),
      ∀ z : X.presheaf.stalk x,
        ((e z : ↥(SemistableModel.localRing X φ x)) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField z) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_localRing_coe_eq.solution
