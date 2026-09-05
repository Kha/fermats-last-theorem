module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import P2M.Util
public import P2M.Sol.S_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

@[expose] public section

theorem ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * ModularCurve.dedekindEtaUnit) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.solution
