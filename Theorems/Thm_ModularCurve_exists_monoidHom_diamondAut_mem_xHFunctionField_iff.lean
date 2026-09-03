import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff

set_option autoImplicit false

theorem ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hdia : ∀ d : ℕ, Nat.Coprime d M →
      ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
        ModularCurve.IsDiamondAut M d σ) :
    ∃ δ : H →* (ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M),
      (∀ u : H, δ u = ModularCurve.diamondAut M (((u : (ZMod M)ˣ) : ZMod M).val)) ∧
      ∀ x : ModularCurve.x1FunctionField M,
        (x : LaurentSeries ℚ) ∈ ModularCurve.xHFunctionField M H ↔ ∀ u : H, δ u x = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff.solution
