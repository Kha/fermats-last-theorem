import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularForm_alSlash_alSlash
import Theorems.Thm_ModularForm_alSlash_heckeT_comm
import Theorems.Thm_ModularFormClass_heckeT_heckeU_comm
import P2M.Util
namespace P2MW.S_ModularForm_heckeT_trace_alSlash_of_eigen

set_option autoImplicit false

open CuspForm ModularFormClass

theorem solution (q : ℕ) {M : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) k) (lam : ℂ) (hF : CuspForm.heckeTLin k hℓ hℓM F = lam • F) :
    ModularForm.heckeT k ℓ (ModularForm.alSlash A k ⇑F +
        (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k (ModularForm.alSlash A k ⇑F))) =
      lam • (ModularForm.alSlash A k ⇑F +
        (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k (ModularForm.alSlash A k ⇑F))) := by
  have hFinv : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ (⇑F) = ⇑F :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn F γ hγ
  have hTF : ModularForm.heckeT k ℓ ⇑F = lam • ⇑F := by
    have h := congrArg DFunLike.coe hF
    simpa using h
  have hqM : q ∣ M := ⟨A.R, A.hM⟩
  have hcop : Nat.Coprime ℓ q := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun h => hℓM (h.trans hqM)
  have hΓ : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    simp
  rw [ModularForm.alSlash_alSlash A k hFinv, ModularForm.heckeU_smul, ModularForm.heckeT_add,
    ModularForm.heckeT_smul, ModularForm.heckeT_smul, ← ModularForm.alSlash_heckeT_comm A k hℓ hℓM hFinv,
    ModularFormClass.heckeT_heckeU_comm F hΓ hcop, hTF, ModularForm.alSlash_smul, ModularForm.heckeU_smul]
  simp only [smul_add, smul_smul]
  congr 1
  rw [show (q : ℂ) ^ (2 - k) * ((q : ℂ) ^ (k - 2) * lam) = lam * ((q : ℂ) ^ (2 - k) * (q : ℂ) ^ (k - 2)) by
    ring]
