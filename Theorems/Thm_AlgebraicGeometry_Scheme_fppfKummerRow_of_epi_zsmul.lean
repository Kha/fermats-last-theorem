import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.fppfKummerRow_of_epi_zsmul
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (hn : Epi (n • 𝟙 G)) :
    ∃ hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact,
      (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
          fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1).ker =
        (n • AddMonoidHom.id (fppfCohomology specInt G 0)).range ∧
      Function.Exact
        (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
          fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1)
        (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1) ∧
      (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1).range =
        AddMonoidHom.ker (n • AddMonoidHom.id (fppfCohomology specInt G 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul.solution
