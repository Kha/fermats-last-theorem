import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_differentiableOn_smul_span_eq_qmPeriodLattice_of_latticeFrame

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise BigOperators
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_differentiableOn_smul_span_eq_qmPeriodLattice_of_latticeFrame
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
    (hv : ∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball z₀ ε))
    (hfull : ∀ z ∈ Metric.ball z₀ ε, ∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), ∀ i : Fin 4, b₀ i = v i z)
    (A : ℍ[ℚ, a, b] → Fin 4 → Fin 4 → ℤ)
    (hA : ∀ z ∈ Metric.ball z₀ ε, ∀ lam ∈ Λ, ∀ j₀ : Fin 4,
      ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z) = ∑ i, (A lam i j₀ : ℂ) • v i z)
    (τ₀ : UpperHalfPlane) (c₀ : ℂ) (hc₀ : c₀ ≠ 0)
    (h₀ : c₀ • Submodule.span ℤ (Set.range fun i : Fin 4 => v i z₀) = qmPeriodLattice ι Λ τ₀) :
    ∃ (τ : ℂ → UpperHalfPlane) (c : ℂ → ℂ) (y : Fin 4 → ℍ[ℚ, a, b]),
      DifferentiableOn ℂ (fun z => ((τ z : UpperHalfPlane) : ℂ)) (Metric.ball z₀ ε) ∧
      DifferentiableOn ℂ c (Metric.ball z₀ ε) ∧
      τ z₀ = τ₀ ∧ c z₀ = c₀ ∧
      ∀ z ∈ Metric.ball z₀ ε,
        c z ≠ 0 ∧
        c z • Submodule.span ℤ (Set.range fun i : Fin 4 => v i z) = qmPeriodLattice ι Λ (τ z) ∧
        ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_differentiableOn_smul_span_eq_qmPeriodLattice_of_latticeFrame.solution
