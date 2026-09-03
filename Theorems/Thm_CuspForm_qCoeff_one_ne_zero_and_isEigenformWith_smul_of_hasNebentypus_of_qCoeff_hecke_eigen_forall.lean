import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg0 : g ≠ 0) (hε : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        b p * ModularFormClass.qCoeff g n)
    (hU : ∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) :
    ModularFormClass.qCoeff g 1 ≠ 0 ∧
      CuspForm.IsEigenformWith ε ((ModularFormClass.qCoeff g 1)⁻¹ • g) ∧
      ∀ p : ℕ, p.Prime →
        ModularFormClass.qCoeff ((ModularFormClass.qCoeff g 1)⁻¹ • g) p = b p := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall.solution
