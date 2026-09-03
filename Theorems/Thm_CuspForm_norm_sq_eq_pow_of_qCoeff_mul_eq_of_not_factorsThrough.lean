import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.PeterssonCoset.mapGL_apply

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M)
    (hε : ¬ ε.FactorsThrough (M / ℓ)) (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0)
    (hg : CuspForm.HasNebentypus ε g) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (ℓ * n) = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 = (ℓ : ℝ) ^ (k - 1) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.solution
