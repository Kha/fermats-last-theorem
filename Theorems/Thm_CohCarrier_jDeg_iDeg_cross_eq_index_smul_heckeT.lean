import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT

set_option autoImplicit false

theorem CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT {M M' d d' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type*} [AddCommGroup A] (q : ℕ) [NeZero M'] [NeZero d] [NeZero d'] [NeZero q]
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hqd : (q : ℤ) ∣ (d : ℤ)) (hdiv : d = d' * q) (φ : H1 M H A) :
    (jDeg M M' H H' d A h) ((iDeg' M M' H H' d' A h') φ)
      = (((iotaDeg M M' H H' d h).range).subgroupOf (GammaHUpper M H q)).index
          • heckeT M H q A φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT.solution
