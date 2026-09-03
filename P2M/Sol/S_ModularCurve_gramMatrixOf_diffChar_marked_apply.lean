import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import P2M.Util
namespace P2MW.S_ModularCurve_gramMatrixOf_diffChar_marked_apply

open ModularCurve Module

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (x₀ : ι) (y z : {b : ι // b ≠ x₀}) :
    gramMatrixOf e (diffChar (Equiv.optionSubtypeNe x₀)) y z =
      (if y = z then (e y.1 : ℤ) else 0) + (e x₀ : ℤ) := by
  rw [gramMatrixOf_apply, gramMap_diffChar_diffChar]
  rfl
