import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ fX = 𝟙 _)
    (y : Spec (CommRingCat.of k) ⟶ Y) (hy : y ≫ fY = 𝟙 _) :
    IsLocalRing.maximalIdeal ((pullback fX fY).presheaf.stalk
        (pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))) =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk
          (pullback.fst fX fY (pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))))).map
        ((pullback.fst fX fY).stalkMap
          (pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))).hom ⊔
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk
          (pullback.snd fX fY (pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))))).map
        ((pullback.snd fX fY).stalkMap
          (pullback.lift x y (hx.trans hy.symm) (IsLocalRing.closedPoint k))).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section.solution
