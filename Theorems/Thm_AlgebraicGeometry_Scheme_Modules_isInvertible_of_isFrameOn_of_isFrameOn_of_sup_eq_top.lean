import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    {a : Γ(M, U)} {b : Γ(M, V)}
    (ha : Scheme.Modules.IsFrameOn a U) (hb : Scheme.Modules.IsFrameOn b V) (hUV : U ⊔ V = ⊤) :
    Scheme.Modules.IsInvertible M := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top.solution
