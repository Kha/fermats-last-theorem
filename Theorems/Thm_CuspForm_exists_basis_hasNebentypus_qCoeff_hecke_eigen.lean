import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.solution
