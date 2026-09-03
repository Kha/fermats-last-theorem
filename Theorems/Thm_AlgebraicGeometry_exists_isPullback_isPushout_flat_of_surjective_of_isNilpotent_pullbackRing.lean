import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing

set_option autoImplicit false
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent CerednikDrinfeld.SpecialFormal.ModuliPackage~isLocalization_away_pullbackRing_of_comp_eq"

theorem AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {X' X'' Z : Scheme.{0}} (f' : X' ⟶ Spec (CommRingCat.of B')) (f'' : X'' ⟶ Spec (CommRingCat.of B''))
    (fZ : Z ⟶ Spec (CommRingCat.of B))
    (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (k' : X' ⟶ X) (k'' : X'' ⟶ X),
      IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
      IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
      h' ≫ k' = h'' ≫ k'' ∧ IsPushout h' h'' k' k'' ∧
      (Flat f' → Flat f'' → Flat f) ∧
      (Flat f' → Flat f'' → LocallyOfFinitePresentation f' → LocallyOfFinitePresentation f'' →
        LocallyOfFinitePresentation f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.solution
