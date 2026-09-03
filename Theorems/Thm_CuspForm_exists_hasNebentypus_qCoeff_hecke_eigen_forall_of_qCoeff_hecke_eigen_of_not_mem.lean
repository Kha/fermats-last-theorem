import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (S : Set ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hf0 : f ≠ 0) (hε : CuspForm.HasNebentypus ε f)
    (a : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff f (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
        a p * ModularFormClass.qCoeff f n) :
    ∃ (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (b : ℕ → ℂ),
      g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → b p = a p) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      (∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem.solution
