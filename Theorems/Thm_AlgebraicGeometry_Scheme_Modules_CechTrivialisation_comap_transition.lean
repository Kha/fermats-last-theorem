import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.comap_transition
    {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) :
    (τ.comap h).transition s =
      (Y'.presheaf.map (homOfLE (𝒱.comap_inter_le h s)).op).hom ((h.app (𝒱.inter s)).hom (τ.transition s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.solution
