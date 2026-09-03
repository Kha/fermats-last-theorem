import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.eq_of_forall_section_comp_eq_of_dense_of_dualNumber
    (k : Type u) [Field k] [IsAlgClosed k] {X Y S : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ Y)
    (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ (y : Spec (CommRingCat.of k) ⟶ X), y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U →
      ∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))),
        T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ y →
        T ≫ pullback.snd f _ = 𝟙 _ → T ≫ F = T ≫ G) :
    F = G := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber.solution
