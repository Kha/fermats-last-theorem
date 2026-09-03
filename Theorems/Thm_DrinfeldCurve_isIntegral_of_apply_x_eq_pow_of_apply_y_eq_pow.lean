import Definitions.Def_DrinfeldCurve_FunctionField
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow

set_option autoImplicit false

namespace DrinfeldCurve

theorem isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsDomain (CoordRing q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (n : ℕ)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ n)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ n) :
    φ.toRingHom.IsIntegral := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow.solution
