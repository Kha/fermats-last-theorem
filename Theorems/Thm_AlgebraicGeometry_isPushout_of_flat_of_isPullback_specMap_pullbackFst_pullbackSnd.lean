import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent open CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {Y Y' Y'' Y₀ : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat f]
    (f' : Y' ⟶ Spec (CommRingCat.of B')) (f'' : Y'' ⟶ Spec (CommRingCat.of B'')) (f₀ : Y₀ ⟶ Spec (CommRingCat.of B))
    (k' : Y' ⟶ Y) (hk' : IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (k'' : Y'' ⟶ Y) (hk'' : IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (h' : Y₀ ⟶ Y') (hh' : IsPullback h' f₀ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Y₀ ⟶ Y'') (hh'' : IsPullback h'' f₀ f'' (Spec.map (CommRingCat.ofHom φ'')))
    (hcomm : h' ≫ k' = h'' ≫ k'') :
    IsPushout h' h'' k' k'' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd.solution
