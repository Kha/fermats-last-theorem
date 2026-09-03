import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
namespace P2MW.S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem solution
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    (by change Mono f; infer_instance) (by change Epi (cokernel.π f); infer_instance)
