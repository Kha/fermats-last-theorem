import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed"

theorem AlgebraicGeometry.finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    {S : Type u} [CommRing S] {W : Scheme.{u}} (q : W ⟶ Spec (CommRingCat.of S)) [IsFinite q] [Etale q]
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    q.finrank (Spec.map (CommRingCat.ofHom sk) (IsLocalRing.closedPoint k)) =
      Nat.card {w : Spec (CommRingCat.of k) ⟶ W // w ≫ q = Spec.map (CommRingCat.ofHom sk)} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed.solution
