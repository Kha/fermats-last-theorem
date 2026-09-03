import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime

set_option autoImplicit false

open CohCarrier in

theorem CohCarrier.heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime (M q : ℕ) [NeZero M]
    [NeZero q] (A : Type) [AddCommGroup A] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (φ : H1 (M * q) ⊤ A) :
    heckeT (M * q) ⊤ q A (heckeTlower (M * q) ⊤ q A φ)
      = φ + (q - 1) • iDeg' M (M * q) ⊤ ⊤ 1 A h1 (jDeg M (M * q) ⊤ ⊤ 1 A h1 φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime.solution
