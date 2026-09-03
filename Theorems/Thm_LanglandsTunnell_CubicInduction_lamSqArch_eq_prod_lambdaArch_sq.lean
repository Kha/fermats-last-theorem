import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicLambda
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_lamSqArch_eq_prod_lambdaArch_sq

set_option autoImplicit false

open NumberField

theorem LanglandsTunnell.CubicInduction.lamSqArch_eq_prod_lambdaArch_sq
    (K : Type) [Field K] [NumberField K] :
    LanglandsTunnell.CubicInduction.lamSqArch K =
      (∏ w : InfinitePlace K, LanglandsTunnell.CubicLambda.lambdaArch K w) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_lamSqArch_eq_prod_lambdaArch_sq.solution
