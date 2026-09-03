import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one

open scoped MatrixGroups

theorem CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ)
    (hHq : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro W.R W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ X : CuspForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one.solution
