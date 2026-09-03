import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
attribute [-instance] FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

set_option autoImplicit false
open Classical in

theorem ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Z : (ℍ × ℍ) →₀ ℤ,
      (∀ τ : ℍ, ∃ n : ℤ,
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
          2 * n = (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) *
            Z.sum (fun e m =>
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0))) ∧
      ∀ g : CuspForm (Γ) 2,
        (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (Γ), UpperHalfPlane.petersson 2 k g τ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp.solution
