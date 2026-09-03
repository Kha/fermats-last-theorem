import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem CategoryTheory.ShortComplex.shortExact_of_mono_cokernel
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel.solution
