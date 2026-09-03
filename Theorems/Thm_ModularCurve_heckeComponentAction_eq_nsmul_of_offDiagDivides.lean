import Definitions.Def_ModularCurve_ComponentGroupHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeComponentAction_eq_nsmul_of_offDiagDivides

open ModularCurve
namespace ModularCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem heckeComponentAction_eq_nsmul_of_offDiagDivides {e : ι → ℕ} {B : Matrix ι ι ℤ}
    {n : ℤ} (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (hdiv : HeckeOffDiagDivides e B) (x : componentGroup e) :
    heckeComponentAction e B hrow hsym x = n • x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeComponentAction_eq_nsmul_of_offDiagDivides.solution
end ModularCurve
