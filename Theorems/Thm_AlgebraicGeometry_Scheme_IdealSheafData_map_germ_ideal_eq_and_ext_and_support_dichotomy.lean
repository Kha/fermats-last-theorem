import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy {X : Scheme.{u}} :
    (∀ (I : X.IdealSheafData) (x : X) (V W : X.affineOpens) (hV : x ∈ (V : X.Opens)) (hW : x ∈ (W : X.Opens)),
      Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom (I.ideal V) =
        Ideal.map (X.presheaf.germ (W : X.Opens) x hW).hom (I.ideal W)) ∧
    (∀ (I J : X.IdealSheafData),
      (∀ x : X, ∃ (U : X.affineOpens) (hx : x ∈ (U : X.Opens)),
        Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) =
          Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (J.ideal U)) → I = J) ∧
    (∀ (I : X.IdealSheafData) (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)),
      (x ∉ (I.support : Set X) → Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) = ⊤) ∧
      (x ∈ (I.support : Set X) →
        Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy.solution
