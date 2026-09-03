import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsMaximalOrder.exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L : Submodule ℤ (Fin 2 → ℂ))
    (hfull : ∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ L) :
    ∃ (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 ∧ c • L = qmPeriodLattice ι Λ τ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem.solution
