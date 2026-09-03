import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchParam
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
p2m_open "LanglandsTunnell~eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC LanglandsTunnell.RankinSelberg~mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq RSCarrier UnramifiedWhittaker"

open RealArchParam in

theorem LanglandsTunnell.RankinSelberg.exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat
    (A : RealArchParam) (par₀ : ZMod 2) (σ₀ : ℝ)
    (Wr₀ : ℝ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ) (χ : ℝˣ → ℂ)
    (hpar : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₂ → par₀ = a₁)
    (hσ : σ₀ = (A.centralExponent + 1).re)
    (hlt : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hunit : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₂ →
      (u₁ - u₂).re = 0 ∨ ((u₁ - u₂).im = 0 ∧ a₁ = a₂))
    (hparity : ∀ (u₁ u₂ : ℂ) (a₁ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₁ → par₀ = a₁ →
      ∀ t : ℝ, Wr₀ (-t) = (-1 : ℂ) ^ a₁.val * Wr₀ t)
    (hDSvan : ∀ (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), A = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr₀ t = 0)
    (hMel : ∀ b : ZMod 2, (b = par₀ ∨ b = par₀ + A.centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr₀ t + (-1 : ℂ) ^ b.val * Wr₀ (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr₀ t + (-1 : ℂ) ^ b.val * Wr₀ (-t)) / (t : ℂ)) s = (A.twist 0 b).archFactor s)
    (hWAN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      WA₀ (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA₀ h)
    (hχ : ∀ z : ℝˣ, ‖χ z‖ = |(z : ℝ)| ^ σ₀)
    (hZ : ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ), WA₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = χ z * WA₀ h)
    (hdiag : ∀ t : ℝˣ, WA₀ (diagOne t) = Wr₀ (t : ℝ))
    (hWAc : Continuous WA₀)
    (hne : ∃ t : ℝˣ, Wr₀ (t : ℝ) ≠ 0) :
    let WA : GL (Fin 2) ℝ → ℂ := fun h => WA₀ h *
      (((|((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ)| ^ (-σ₀ / 2) : ℝ)) : ℂ)
    ∃ (P : ℝ → ℝ) (x₀ : ℝ) (Hinf : ℂ → ℂ),
      Measurable P ∧
      (∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
        WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * (starRingEnd ℂ) (WA (upperUnit a₁ 0 a₂ h₁ h₂.ne')) = ((P (a₁ / a₂) : ℝ) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ P y) ∧
      (¬ ∀ᵐ y : ℝ, P y = 0) ∧
      (∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2))) ∧
      (∀ σ' : ℝ, (-1 : ℝ) < σ' → AnalyticAt ℂ Hinf (σ' : ℂ)) ∧
      Hinf 0 = 0 ∧
      (∀ s : ℂ, max x₀ 0 < s.re →
        Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat.solution
