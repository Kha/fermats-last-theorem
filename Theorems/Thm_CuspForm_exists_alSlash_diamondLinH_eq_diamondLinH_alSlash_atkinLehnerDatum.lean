import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum

open scoped MatrixGroups

theorem CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (d : (ZMod M)ˣ) (f G : CuspForm (CohCarrier.GammaH M H) k)
    (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ∃ d' : (ZMod M)ˣ,
      ZMod.unitsMap (Dvd.intro_left q W.hM.symm : W.R ∣ M) d' = ZMod.unitsMap (Dvd.intro_left q W.hM.symm : W.R ∣ M) d ∧
      ZMod.unitsMap (Dvd.intro W.R W.hM.symm : q ∣ M) (d' * d) = 1 ∧
      ModularForm.alSlash W k (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) =
        (⇑(CuspForm.diamondLinH k d' G) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum.solution
