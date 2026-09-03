import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_forall_exists_mulVec_eq_iff_smul_mem_qmPeriodLattice_of_im_neg
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsMaximalOrder.exists_forall_exists_mulVec_eq_iff_smul_mem_qmPeriodLattice_of_im_neg
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : ℂ) (hτ : τ.im < 0) :
    ∃ (τ' : UpperHalfPlane) (c : ℂ), c ≠ 0 ∧
      ∀ w : Fin 2 → ℂ, (∃ x ∈ Λ, ((ι x).map (algebraMap ℝ ℂ)).mulVec ![τ, 1] = w) ↔ c • w ∈ qmPeriodLattice ι Λ τ' := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_forall_exists_mulVec_eq_iff_smul_mem_qmPeriodLattice_of_im_neg.solution
