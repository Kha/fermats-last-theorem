import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_one_iso_id

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_one_iso_id (X : Scheme.{u}) :
    Nonempty (Scheme.Modules.exteriorPower X 1 ≅ 𝟭 X.Modules) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_one_iso_id.solution
