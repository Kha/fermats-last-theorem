import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff

set_option autoImplicit false

theorem ModularCurve.exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
    (M₀ t : ℕ) [NeZero M₀] [NeZero t] (hM₀t : Nat.Coprime M₀ t)
    (hdia : ∀ d : ℕ, Nat.Coprime d (M₀ * t) →
      ∃ σ : ModularCurve.x1FunctionField (M₀ * t) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * t),
        ModularCurve.IsDiamondAut (M₀ * t) d σ) :
    ∃ δ : (ZMod.unitsMap (dvd_mul_right M₀ t)).ker →*
        (ModularCurve.x1FunctionField (M₀ * t) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * t)),
      (∀ u : (ZMod.unitsMap (dvd_mul_right M₀ t)).ker,
          δ u = ModularCurve.diamondAut (M₀ * t)
            (((u : (ZMod (M₀ * t))ˣ) : ZMod (M₀ * t)).val)) ∧
      ∀ x : ModularCurve.x1FunctionField (M₀ * t),
        (x : LaurentSeries ℚ) ∈ ModularCurve.x1x0FunctionFieldC ℚ M₀ t ↔
          ∀ u : (ZMod.unitsMap (dvd_mul_right M₀ t)).ker, δ u x = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff.solution
