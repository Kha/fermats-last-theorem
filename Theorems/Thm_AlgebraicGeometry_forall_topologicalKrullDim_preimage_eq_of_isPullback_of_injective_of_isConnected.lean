import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (hs : Smooth f₀) (hp : IsProper f₀)
    (hconn : ∀ t : ↥(Spec (CommRingCat.of R₀)), _root_.IsConnected (f₀.base ⁻¹' {t}))
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of L)) (g : A ⟶ A₀)
    (hg : IsPullback g f f₀ (Spec.map (CommRingCat.ofHom φ)))
    (d : ℕ) (hdim : ∀ x : ↥(Spec (CommRingCat.of L)), topologicalKrullDim ↥(f.base ⁻¹' {x}) = d)
    (t : ↥(Spec (CommRingCat.of R₀))) : topologicalKrullDim ↥(f₀.base ⁻¹' {t}) = d := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected.solution
