module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import P2M.Util
public import P2M.Sol.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4

@[expose] public section

theorem ModularCurve.qExpansion_E4_eq_map_eisenstein4 : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.solution
