import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_smul_qmPeriodLattice_eq_iff_exists_fuchsianGroup_smul_eq_of_level_one

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsMaximalOrder.exists_smul_qmPeriodLattice_eq_iff_exists_fuchsianGroup_smul_eq_of_level_one
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ τ' : UpperHalfPlane) :
    (∃ c : ℂ, c ≠ 0 ∧ c • qmPeriodLattice ι Λ τ = qmPeriodLattice ι Λ τ') ↔
      ∃ γ ∈ fuchsianGroup Λ ι, γ • τ = τ' := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_smul_qmPeriodLattice_eq_iff_exists_fuchsianGroup_smul_eq_of_level_one.solution
