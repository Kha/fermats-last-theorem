import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime

set_option autoImplicit false

theorem CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime {M : ℕ} {H : Subgroup (ZMod M)ˣ}
    {q : ℕ} {A : Type} [AddCommGroup A] {M' d d' : ℕ} {H' : Subgroup (ZMod M')ˣ}
    [NeZero M] [NeZero q] [NeZero d] [NeZero d'] [NeZero M']
    (hcop : Nat.Coprime q M)
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hdqM' : ((d * q : ℕ) : ℤ) ∣ (M' : ℤ)) (hdiv : d' = d * q) (φ : H1 M H A) :
    jDeg M M' H H' d A h (iDeg' M M' H H' d' A h' φ)
      = ((iotaDeg M M' H H' d h).range.subgroupOf (GammaHLower M H q)).index
          • heckeTlower M H q A φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime.solution
