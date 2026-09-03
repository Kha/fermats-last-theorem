import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_module_finite_residueField_restrict

open AlgebraicCurve
theorem AlgebraicCurve.Place.module_finite_residueField_restrict (K F F' : Type*)
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_module_finite_residueField_restrict.solution
