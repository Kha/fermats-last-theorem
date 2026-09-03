import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_AdicThickening
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion~eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj GoodReductionJacobian NeronModelInfra"

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hone : ∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫ adicThickeningι f I n = adicThickeningBase I n ≫ e.1)
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (hmul : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x y : SchemeHomOver t (adicThickeningToBase f I n)),
        pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
            (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ m =
          ((L n).mul t x y).1 ≫ adicThickeningι f I n)
    (i : A ⟶ A) (hi : i ≫ f = f)
    (hinv : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x : SchemeHomOver t (adicThickeningToBase f I n)),
        x.1 ≫ adicThickeningι f I n ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n) :
    pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A ∧
    pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A ∧
    pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m =
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
              (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                ← pullback.condition (f := f) (g := f)]) ≫ m ∧
    pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]) ≫ m = f ≫ e.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.solution
