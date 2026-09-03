import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.IsEichlerOrder.forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :

    (∀ M : Submodule ℤ (Fin 2 → ℂ),
      (M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧
        (∀ v ∈ qmPeriodLattice ι J' τ, (ℓ : ℂ) • v ∈ M → v ∈ qmPeriodLattice ι Λ τ)) ↔
      ∃ t ∈ R, nrd t = (ℓ : ℚ) ∧
        (∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ∧
        (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ m ∈ M, (ℓ : ℂ) • w + m = v) ↔
          ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v)) ∧

    (∀ t t' : ℍ[ℚ, a, b], t ∈ R → t' ∈ R → nrd t = (ℓ : ℚ) → nrd t' = (ℓ : ℚ) →
      (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
        ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) →
      (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ↔ (∃ y ∈ Λ, qmPeriodMap ι τ (y * t') = v)) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * t = t') ∧

    (∀ t : ℍ[ℚ, a, b], t ∈ R → nrd t = (ℓ : ℚ) →
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι t ∧ 0 < g.det.val ∧
        (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ↔
          v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ)) ∧
        (∀ v : Fin 2 → ℂ, (∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
          v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι J' (g • τ))) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq.solution
