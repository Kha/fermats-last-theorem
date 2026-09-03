import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g h : CuspForm (Gamma1 M) k)
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
      g τ' = (τ : ℂ) ^ k * h τ) :
    CuspForm.HasNebentypus ε⁻¹ h ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ lam : ℂ,
        (∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          lam * ModularFormClass.qCoeff g n) →
        ∀ n : ℕ, ModularFormClass.qCoeff h (p * n) +
            ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) =
          ε⁻¹ (p : ZMod M) * lam * ModularFormClass.qCoeff h n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.solution
