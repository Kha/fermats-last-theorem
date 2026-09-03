import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_relativeGroupLaw_one_eq_of_forall_exists_away
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hloc : ∀ s : Spec (CommRingCat.of R), ∃ (r : R), r ∉ s.asIdeal ∧
      ∃ L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))),
        (L.one (𝟙 _)).1 = pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]))
    (huniq : ∀ (r : R) (L L' : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))),
        L.one (𝟙 _) = L'.one (𝟙 _) → L = L') :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away.solution
