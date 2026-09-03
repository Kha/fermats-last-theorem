import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_sup_eq_top
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔛 : X.OrderedAffineCover) (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover) :
    Nonempty ((U : Scheme.{u}).OrderedAffineCover) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top.solution
