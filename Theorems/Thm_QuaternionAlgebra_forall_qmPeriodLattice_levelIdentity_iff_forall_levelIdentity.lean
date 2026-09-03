import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ J' : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b]) (ℓ : ℕ) (τ : UpperHalfPlane) :
    (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
        ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity.solution
