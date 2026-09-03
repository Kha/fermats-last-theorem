import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent open CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem AlgebraicGeometry.exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent
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
      IsClosedImmersion k' ∧ IsClosedImmersion k'' ∧ Function.Bijective k'.base ∧ Function.Bijective k''.base ∧
      (Flat f' → Flat f'' → Flat f) ∧ (IsProper f' → IsProper f) ∧ (Smooth f' → Smooth f'' → Smooth f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isPushout_isPullback_specMap_pullbackFst_pullbackSnd_of_surjective_of_isNilpotent.solution
