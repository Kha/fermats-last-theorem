import Definitions.Def_ModularCurve_JZeroGoodReductionV2
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import P2M.Util
import P2M.Sol.S_ModularCurve_mazurQuotientSpecialization_heckeModuleBar_of_doorV2

open ModularCurve AlgebraicCurve IsLocalRing
set_option synthInstance.maxHeartbeats 80000 in
theorem ModularCurve.mazurQuotientSpecialization_heckeModuleBar_of_doorV2 (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p)
    (hdiv : ∀ m : ℤ, m ≠ 0 → ∀ x : JZero p, ∃ y : JZero p, m • y = x)
    (hdoor : ∀ ℓ : ℕ, (hℓp : ℓ.Prime) → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        letI := heckeModuleBar p
        ∃ _ : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)),
        ∃ D : JZeroGoodReductionSpecialization A ℓ hℓp p,
          TorsBijFor ℓ D.sp ∧
          FTorsionFor (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)) ∧
          RaynaudFor ℓ D.sp ∧ CuspRuleFor A D.sp) :
    MazurQuotientSpecialization p (heckeModuleBar p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mazurQuotientSpecialization_heckeModuleBar_of_doorV2.solution
