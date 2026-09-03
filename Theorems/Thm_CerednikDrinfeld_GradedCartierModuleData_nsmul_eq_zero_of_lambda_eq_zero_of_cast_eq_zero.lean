import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) (hp : (p : B) = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (z : D.NMod) (hz : D.lambda z = 0) :
    p • z = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_eq_zero_of_lambda_eq_zero_of_cast_eq_zero.solution
