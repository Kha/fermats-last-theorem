import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.solution
