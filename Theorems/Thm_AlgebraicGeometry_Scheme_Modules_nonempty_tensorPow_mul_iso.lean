import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_tensorPow_mul_iso

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_tensorPow_mul_iso {X : Scheme.{u}} (L : X.Modules) (a b : ℕ) :
    Nonempty (L.tensorPow (a * b) ≅ (L.tensorPow a).tensorPow b) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_tensorPow_mul_iso.solution
