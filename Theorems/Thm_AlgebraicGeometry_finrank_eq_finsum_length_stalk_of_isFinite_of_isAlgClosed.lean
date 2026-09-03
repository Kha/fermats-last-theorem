import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    (s : ↥(Spec (CommRingCat.of k))) :
    (f.finrank s : ℕ∞) =
      ∑ᶠ x : {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))},
        Module.length (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k)))
          (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed.solution
