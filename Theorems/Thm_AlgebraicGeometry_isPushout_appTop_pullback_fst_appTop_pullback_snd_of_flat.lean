import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
    {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type u) [CommRing A] [Algebra k A] [Module.Flat k A] :
    IsPushout (CommRingCat.ofHom (algebraMap k A))
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)
      (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.solution
