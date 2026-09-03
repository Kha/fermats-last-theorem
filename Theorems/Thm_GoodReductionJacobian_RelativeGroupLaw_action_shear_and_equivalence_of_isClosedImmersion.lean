import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.action_shear_and_equivalence_of_isClosedImmersion
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    L.action i ≫ f = CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ f ∧
    (∃ σ : CategoryTheory.Limits.pullback (i ≫ f) f ≅ CategoryTheory.Limits.pullback (i ≫ f) f,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = L.action i ∧
      σ.hom ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) f = CategoryTheory.Limits.pullback.fst (i ≫ f) f) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f),
      a ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = b ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f → a ≫ L.action i = b ≫ L.action i → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ G =>
      ∃ φ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f, φ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = x ∧ φ ≫ L.action i = y) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.solution
