import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import P2M.Util
import P2M.Sol.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash
    (M : ℕ) [NeZero M] (p : ℕ) (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (d : (ZMod M)ˣ) (f G : CuspForm (CohCarrier.GammaH M H) k)
    (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ∃ d' : (ZMod M)ˣ,
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d' = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∧
      ZMod.unitsMap hpM (d' * d) = 1 ∧
      ModularForm.alSlash W k (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) =
        (⇑(CuspForm.diamondLinH k d' G) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash.solution
