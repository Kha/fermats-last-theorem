import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (hF : ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (hβdef : ModularCurve.HeckeBetaOneDefined N ℓ)
    (hdeg : AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L N ℓ) = ℓ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ)
    (y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ)))) :
    letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeBetaOneBar L N ℓ)
    ((ModularCurve.heckeBetaOneBar L N ℓ
        (Algebra.norm (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) y) :
          ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ)))) : LaurentSeries L) =
      ∏ i : Fin ℓ, ModularCurve.qTwist (ζ ^ (i : ℕ)) ((y : ↥(ModularCurve.laurentBaseChange L
        (ModularCurve.x1x0FunctionFieldC ℚ N (N * ℓ)))) : LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq.solution
