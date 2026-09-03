import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

set_option autoImplicit false

open ModularFormClass
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) * (p : ZMod W.R) = 1)
    (a : ℕ) (ha : 3 ≤ a) (ha2 : Even a) (hpa : p - 1 ∣ a)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (w : ℤ) (hw : 2 ≤ w) (F : CuspForm (CohCarrier.GammaH M H) w)
    (hFint : ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff F n)
    (hFW : ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash W w ⇑(CuspForm.diamondLinH w d F)) n) :
    ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) (w + i * a),
        (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n) ∧
        (∀ (n : ℕ) (x y x' y' : integralClosure ℤ ℂ), y ∉ 𝔪 → y' ∉ 𝔪 →
          (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.solution
