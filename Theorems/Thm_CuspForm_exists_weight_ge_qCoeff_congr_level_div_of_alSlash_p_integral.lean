import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply
set_option autoImplicit false
open ModularFormClass

theorem CuspForm.exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N' : ℕ) [NeZero N']
    (A : ModularForm.AtkinLehnerDatum (p * N') p)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (w : ℤ) (hw : 2 ≤ w) (F : CuspForm (CongruenceSubgroup.Gamma0 (p * N')) w)
    (hFint : ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff F n)
    (hFW : ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash A w ⇑F) n) :
    ∃ (k : ℤ) (G : CuspForm (CongruenceSubgroup.Gamma0 N') k),
      w ≤ k ∧ ((p : ℤ) - 1 ∣ k - w) ∧
      (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n) ∧
      (∀ (n : ℕ) (x y x' y' : integralClosure ℤ ℂ), y ∉ 𝔪 → y' ∉ 𝔪 →
        (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral.solution
