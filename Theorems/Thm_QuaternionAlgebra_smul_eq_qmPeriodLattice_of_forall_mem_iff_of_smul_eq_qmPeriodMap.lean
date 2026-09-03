import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise BigOperators
open QuaternionAlgebra

theorem QuaternionAlgebra.smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) [NeZero N]
    (D : Set ℂ) (z₀ : ℂ) (hz₀ : z₀ ∈ D)
    (L ME : ℂ → Submodule ℤ (Fin 2 → ℂ)) (κ c : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
    (y : Fin 4 → ℍ[ℚ, a, b]) (τ : ℂ → UpperHalfPlane) (T : Set (Fin 4 → ℤ))
    (hκ : ∀ z ∈ D, κ z ≠ 0) (hc : ∀ z ∈ D, c z ≠ 0)
    (hbasis : ∀ z ∈ D,
      (∀ i : Fin 4, v i z ∈ κ z • L z) ∧ ∀ x ∈ κ z • L z, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x)
    (hME : ∀ z ∈ D, ∀ w : Fin 2 → ℂ,
      w ∈ ME z ↔ ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (L z).toAddSubgroup) =
        (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (L z).toAddSubgroup))
    (hper : ∀ z ∈ D, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i))
    (h₀ : (c z₀ * κ z₀) • ME z₀ = qmPeriodLattice ι J' (τ z₀)) :
    ∀ z ∈ D, (c z * κ z) • ME z = qmPeriodLattice ι J' (τ z) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap.solution
