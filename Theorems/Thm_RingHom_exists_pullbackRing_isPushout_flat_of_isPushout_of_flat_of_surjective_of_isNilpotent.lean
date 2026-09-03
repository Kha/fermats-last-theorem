import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
    (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
    (H' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom a') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g'))
    (H'' : IsPushout (CommRingCat.ofHom φ'') (CommRingCat.ofHom a'') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g''))
    (hfl' : a'.Flat) (hfl'' : a''.Flat) :
    ∃ a : pullbackRing φ' φ'' →+* pullbackRing g' g'',
      (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ'') ∧
      (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'') ∧

      IsPullback (CommRingCat.ofHom (pullbackFst g' g'')) (CommRingCat.ofHom (pullbackSnd g' g''))
        (CommRingCat.ofHom g') (CommRingCat.ofHom g'') ∧
      Function.Surjective g'' ∧ (∀ x ∈ RingHom.ker g'', IsNilpotent x) ∧

      IsPushout (CommRingCat.ofHom (pullbackFst φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a')
        (CommRingCat.ofHom (pullbackFst g' g'')) ∧
      IsPushout (CommRingCat.ofHom (pullbackSnd φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a'')
        (CommRingCat.ofHom (pullbackSnd g' g'')) ∧

      a.Flat ∧ (a'.FinitePresentation → a''.FinitePresentation → a.FinitePresentation) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent.solution
