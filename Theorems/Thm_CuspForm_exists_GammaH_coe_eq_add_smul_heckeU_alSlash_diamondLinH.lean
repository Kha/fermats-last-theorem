import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k)
    (d' : (ZMod M)ˣ)
    (hd' : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d' : ZMod W.R) * (p : ZMod W.R) = 1) :
    ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) k,
      ⇑G = ⇑F + (p : ℂ) ^ (2 - k) •
        ModularForm.heckeU k p (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d' F)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH.solution
