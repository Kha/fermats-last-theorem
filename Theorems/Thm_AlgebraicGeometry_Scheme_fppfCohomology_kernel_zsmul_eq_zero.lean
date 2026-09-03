import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_fppfCohomology_kernel_zsmul_eq_zero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.fppfCohomology_kernel_zsmul_eq_zero
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (k : ℕ)
    (x : fppfCohomology specInt (kernel (n • 𝟙 G)) k) : n • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_fppfCohomology_kernel_zsmul_eq_zero.solution
