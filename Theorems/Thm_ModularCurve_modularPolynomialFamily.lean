module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import P2M.Util
public import P2M.Sol.S_ModularCurve_modularPolynomialFamily

@[expose] public section
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.modularPolynomialFamily : ModularPolynomialFamily := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularPolynomialFamily.solution
