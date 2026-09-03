import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four

set_option autoImplicit false

open scoped Quaternion

theorem solution {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩
  have hr : Module.rank ℤ Λ = Module.rank ℚ ℍ[ℚ, a, b] := Submodule.IsLattice.rank' ℚ Λ
  rw [QuaternionAlgebra.rank_eq_four] at hr
  exact Module.finrank_eq_of_rank_eq hr
