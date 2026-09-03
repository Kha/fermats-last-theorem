import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_shortExact_map_tensorRight_of_splitting

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
theorem Rep.shortExact_map_tensorRight_of_splitting {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (B : Rep.{u} k G) :
    (X.map (MonoidalCategory.tensorRight B)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_tensorRight_of_splitting.solution
