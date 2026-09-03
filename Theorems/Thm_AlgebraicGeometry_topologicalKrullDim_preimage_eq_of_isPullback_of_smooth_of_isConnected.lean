import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected"

theorem AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
    {X S X' S' : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f) (b : S' ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (hg : IsPullback g f' f b) (s' : ↥S') (hconn : _root_.IsConnected (f.base ⁻¹' {b.base s'})) :
    topologicalKrullDim ↥(f'.base ⁻¹' {s'}) = topologicalKrullDim ↥(f.base ⁻¹' {b.base s'}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected.solution
