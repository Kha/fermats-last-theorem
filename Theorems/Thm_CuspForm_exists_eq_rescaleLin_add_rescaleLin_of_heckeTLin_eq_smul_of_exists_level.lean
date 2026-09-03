import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

set_option autoImplicit false

open CongruenceSubgroup

theorem CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : 1 * M ∣ M * p) (hp : p * M ∣ M * p)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (f : CuspForm (Gamma0 (M * p)) 2)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M * p), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN f = a ℓ • f)
    (hocc : ∃ g : CuspForm (Gamma0 M) 2, g ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ¬ ℓ ∣ M * p), ℓ ∉ S →
        CuspForm.heckeTLin 2 hℓ hℓM g = a ℓ • g) :
    ∃ h₁ h₂ : CuspForm (Gamma0 M) 2,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ¬ ℓ ∣ M * p), ℓ ∉ S →
        CuspForm.heckeTLin 2 hℓ hℓM h₁ = a ℓ • h₁ ∧ CuspForm.heckeTLin 2 hℓ hℓM h₂ = a ℓ • h₂) ∧
      f = FreyPackage.ModMCarrier.rescaleLin h1 2 h₁ + FreyPackage.ModMCarrier.rescaleLin hp 2 h₂ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level.solution
