import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage open AlgebraicGeometry hiding isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent

theorem AlgebraicGeometry.isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))

    {X X' X'' XZ : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat fX]
    (fX' : X' ⟶ Spec (CommRingCat.of B')) (fX'' : X'' ⟶ Spec (CommRingCat.of B'')) (fXZ : XZ ⟶ Spec (CommRingCat.of B))
    (hX' : XZ ⟶ X') (cXh' : IsPullback hX' fXZ fX' (Spec.map (CommRingCat.ofHom φ')))
    (hX'' : XZ ⟶ X'') (cXh'' : IsPullback hX'' fXZ fX'' (Spec.map (CommRingCat.ofHom φ'')))
    (kX' : X' ⟶ X) (cXk' : IsPullback kX' fX' fX (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (kX'' : X'' ⟶ X) (cXk'' : IsPullback kX'' fX'' fX (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (poX : IsPushout hX' hX'' kX' kX'')

    {Y Y' Y'' YZ : Scheme.{0}}
    (fY : Y ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat fY]
    (fY' : Y' ⟶ Spec (CommRingCat.of B')) (fY'' : Y'' ⟶ Spec (CommRingCat.of B'')) (fYZ : YZ ⟶ Spec (CommRingCat.of B))
    (hY' : YZ ⟶ Y') (cYh' : IsPullback hY' fYZ fY' (Spec.map (CommRingCat.ofHom φ')))
    (hY'' : YZ ⟶ Y'') (cYh'' : IsPullback hY'' fYZ fY'' (Spec.map (CommRingCat.ofHom φ'')))
    (kY' : Y' ⟶ Y) (cYk' : IsPullback kY' fY' fY (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (kY'' : Y'' ⟶ Y) (cYk'' : IsPullback kY'' fY'' fY (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (poY : IsPushout hY' hY'' kY' kY'') :
    IsPushout
      (pullback.map fXZ fYZ fX' fY' hX' hY' (Spec.map (CommRingCat.ofHom φ')) cXh'.w.symm cYh'.w.symm)
      (pullback.map fXZ fYZ fX'' fY'' hX'' hY'' (Spec.map (CommRingCat.ofHom φ'')) cXh''.w.symm cYh''.w.symm)
      (pullback.map fX' fY' fX fY kX' kY' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) cXk'.w.symm cYk'.w.symm)
      (pullback.map fX'' fY'' fX fY kX'' kY'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) cXk''.w.symm cYk''.w.symm) ∧
    IsPullback (pullback.map fX' fY' fX fY kX' kY' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) cXk'.w.symm cYk'.w.symm)
      (pullback.fst fX' fY' ≫ fX') (pullback.fst fX fY ≫ fX) (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
    IsPullback (pullback.map fX'' fY'' fX fY kX'' kY'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) cXk''.w.symm cYk''.w.symm)
      (pullback.fst fX'' fY'' ≫ fX'') (pullback.fst fX fY ≫ fX) (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat.solution
