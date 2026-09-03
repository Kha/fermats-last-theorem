import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_eq_smul_of_forall_mulVec_comm

set_option autoImplicit false

open scoped Quaternion MatrixGroups
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsOrder.exists_eq_smul_of_forall_mulVec_comm
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (hM : ∀ x ∈ Λ, ∀ v : Fin 2 → ℂ, M (((ι x).map (algebraMap ℝ ℂ)).mulVec v) = ((ι x).map (algebraMap ℝ ℂ)).mulVec (M v)) :
    ∃ c : ℂ, ∀ v : Fin 2 → ℂ, M v = c • v := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_eq_smul_of_forall_mulVec_comm.solution
