import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsMaximalOrder.exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L : Submodule ℤ (Fin 2 → ℂ))
    (hfull : ∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ L) :
    ∃ (τ : ℂ) (c : ℂ), τ.im ≠ 0 ∧ c ≠ 0 ∧
      ∀ w : Fin 2 → ℂ, w ∈ c • L ↔ ∃ x ∈ Λ, ((ι x).map (algebraMap ℝ ℂ)).mulVec ![τ, 1] = w := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem.solution
