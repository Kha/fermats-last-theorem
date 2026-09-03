import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [Smooth f]
    (hconn : ∀ s : ↥(Spec (CommRingCat.of S)), _root_.IsConnected (f.base ⁻¹' {s}))
    (n : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = n)
    (s' : ↥(Spec (CommRingCat.of S'))) :
    topologicalKrullDim ↥((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).base ⁻¹' {s'}) = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected.solution
