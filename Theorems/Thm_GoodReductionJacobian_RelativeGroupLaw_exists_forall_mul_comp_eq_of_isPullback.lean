import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_comp_eq_of_isPullback
    {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] {A A' : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
    (L : RelativeGroupLaw S f) :
    ∃ L' : RelativeGroupLaw B f',
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of B)) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ g =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)))
            ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of B)),
        (L'.one t').1 ≫ g = (L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)))).1) ∧
      (L.IsCommutative → L'.IsCommutative) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback.solution
