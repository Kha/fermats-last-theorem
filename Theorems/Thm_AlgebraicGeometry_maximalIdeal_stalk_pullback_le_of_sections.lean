import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.maximalIdeal_stalk_pullback_le_of_sections
    {k : Type u} [Field k] {Y Z : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ pY = 𝟙 _) (z : Spec (.of k) ⟶ Z) (hz : z ≫ pZ = 𝟙 _)
    (w : ↑(pullback pY pZ)) (hw : w = (pullback.lift y z (hy.trans hz.symm)) (closedPoint k)) :
    maximalIdeal ((pullback pY pZ).presheaf.stalk w) ≤
      (maximalIdeal _).map ((pullback.fst pY pZ).stalkMap w).hom ⊔
        (maximalIdeal _).map ((pullback.snd pY pZ).stalkMap w).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections.solution
