import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_pullback_residue_of_forall_isReduced_stalk_quotient

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_pullback_residue_of_forall_isReduced_stalk_quotient
    {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A))
    (h : ∀ x : X, toBase.base x = IsLocalRing.closedPoint A →
      _root_.IsReduced (X.presheaf.stalk x ⧸
        Ideal.map ((X.presheaf.germ ⊤ x trivial).hom.comp
          (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
          (IsLocalRing.maximalIdeal A))) :
    IsReduced (pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_pullback_residue_of_forall_isReduced_stalk_quotient.solution
