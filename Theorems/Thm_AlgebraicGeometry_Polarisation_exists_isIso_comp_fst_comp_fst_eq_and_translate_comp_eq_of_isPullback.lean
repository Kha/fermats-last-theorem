import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
    {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of T)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw T f')
    (gA : A' ⟶ A) (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T'' : Scheme.{0}} (t'' : T'' ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t'' f'),
      (L'.mul t'' x y).1 ≫ gA =
        (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (x₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) f')
    (hx : x.1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ x₀.1) :
    ∃ κ : pullback f' (𝟙 (Spec (CommRingCat.of T))) ⟶
        pullback (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)),
      IsIso κ ∧
      κ ≫ pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
          pullback.fst f (𝟙 (Spec (CommRingCat.of S))) =
        pullback.fst f' (𝟙 (Spec (CommRingCat.of T))) ≫ gA ∧
      Polarisation.translate f' L' (𝟙 (Spec (CommRingCat.of T))) x ≫ κ ≫
          pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) =
        κ ≫ pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
          Polarisation.translate f L (𝟙 (Spec (CommRingCat.of S))) x₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback.solution
