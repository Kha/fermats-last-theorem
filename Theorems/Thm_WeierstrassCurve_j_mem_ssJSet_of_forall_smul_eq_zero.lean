import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero

set_option autoImplicit false

theorem WeierstrassCurve.j_mem_ssJSet_of_forall_smul_eq_zero {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (W : WeierstrassCurve κ) [W.IsElliptic]
    (hss : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0) :
    W.j ∈ ModularCurve.ssJSet q' κ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero.solution
