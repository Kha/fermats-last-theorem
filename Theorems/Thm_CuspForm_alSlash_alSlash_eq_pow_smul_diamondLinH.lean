import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH

set_option autoImplicit false

open scoped ModularForm MatrixGroups
theorem CuspForm.alSlash_alSlash_eq_pow_smul_diamondLinH
    (M : ℕ) [NeZero M] (p : ℕ) (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : ZMod (M / p)) = (p : ZMod (M / p)))
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W k (ModularForm.alSlash W k (⇑f)) =
      ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH.solution
