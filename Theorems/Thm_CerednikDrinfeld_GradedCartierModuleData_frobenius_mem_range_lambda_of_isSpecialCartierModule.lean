import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.frobenius_mem_range_lambda_of_isSpecialCartierModule
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) (x : D.M) :
    D.frobenius x ∈ LinearMap.range D.lambda := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule.solution
