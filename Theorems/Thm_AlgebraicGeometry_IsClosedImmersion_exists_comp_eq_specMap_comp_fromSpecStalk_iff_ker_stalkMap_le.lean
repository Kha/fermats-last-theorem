import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
    {A K : Scheme.{0}} (κ : K ⟶ A) [IsClosedImmersion κ] (y' : K)
    (J : Ideal (A.presheaf.stalk (κ.base y'))) :
    (∃ t : Spec (CommRingCat.of ((A.presheaf.stalk (κ.base y')) ⧸ J)) ⟶ K,
        t ≫ κ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ A.fromSpecStalk (κ.base y')) ↔
      RingHom.ker (κ.stalkMap y').hom ≤ J := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le.solution
