import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p) [NeZero W.R]
    (H' : Subgroup (ZMod W.R)ˣ) (k : ℤ) (G : CuspForm (CohCarrier.GammaH W.R H') k)
    (d₀ : (ZMod W.R)ˣ) (hd₀ : (d₀ : ZMod W.R) = (p : ZMod W.R)) :
    ModularForm.alSlash W k ⇑G = (⇑(CuspForm.diamondLinH k d₀ G)) ∣[k] ModularForm.heckeDiagMatrix p := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix.solution
