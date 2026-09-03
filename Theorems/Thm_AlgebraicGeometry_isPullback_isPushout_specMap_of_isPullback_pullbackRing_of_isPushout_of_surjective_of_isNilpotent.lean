import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent CerednikDrinfeld.SpecialFormal.ModuliPackage"

theorem AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A A' A'' A₀ : CommRingCat.{0}}
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {g' : A' ⟶ A₀} {g'' : A'' ⟶ A₀} (hA : IsPullback a' a'' g' g'')
    (u : CommRingCat.of ↥(pullbackRing φ' φ'') ⟶ A) (s' : CommRingCat.of B' ⟶ A') (s'' : CommRingCat.of B'' ⟶ A'')
    (s₀ : CommRingCat.of B ⟶ A₀)
    (hu' : CommRingCat.ofHom (pullbackFst φ' φ'') ≫ s' = u ≫ a')
    (hu'' : CommRingCat.ofHom (pullbackSnd φ' φ'') ≫ s'' = u ≫ a'')
    (hg' : CommRingCat.ofHom φ' ≫ s₀ = s' ≫ g') (hg'' : CommRingCat.ofHom φ'' ≫ s₀ = s'' ≫ g'')
    (hco' : IsPushout (CommRingCat.ofHom φ') s' s₀ g') (hco'' : IsPushout (CommRingCat.ofHom φ'') s'' s₀ g'') :
    IsPullback (Spec.map a') (Spec.map s') (Spec.map u) (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
    IsPullback (Spec.map a'') (Spec.map s'') (Spec.map u) (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
    IsPushout (Spec.map g') (Spec.map g'') (Spec.map a') (Spec.map a'') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent.solution
