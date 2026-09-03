import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp

set_option autoImplicit false

open ModularFormClass
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {k : ℤ} (hk : Even k) (F : CuspForm (CohCarrier.GammaH M H) k) (P : PowerSeries ℤ) (hF : ModularCurve.IsIntegralQExp F P) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d F)) n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp.solution
