import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u
theorem AlgebraicGeometry.Scheme.nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
    (S : Scheme.{u}) (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (k : ℕ)
    (hF : ∀ (U : S.Fppf) (s : F.1.obj (Opposite.op U)), k • s = 0)
    (n : ℕ) (x : fppfCohomology S F n) :
    k • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero.solution
