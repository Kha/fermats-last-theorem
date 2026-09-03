import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import P2M.Util
import P2M.Sol.S_ModularCurve_gramMatrixOf_diffChar_marked_apply

open ModularCurve Module
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem gramMatrixOf_diffChar_marked_apply (e : ι → ℕ) (x₀ : ι) (y z : {b : ι // b ≠ x₀}) :
    gramMatrixOf e (diffChar (Equiv.optionSubtypeNe x₀)) y z =
      (if y = z then (e y.1 : ℤ) else 0) + (e x₀ : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_gramMatrixOf_diffChar_marked_apply.solution
end ModularCurve
