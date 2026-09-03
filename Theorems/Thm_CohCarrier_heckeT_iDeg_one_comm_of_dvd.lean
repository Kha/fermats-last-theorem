import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_one_comm_of_dvd {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hqN : q ∣ N) (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
      = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_iDeg_one_comm_of_dvd.solution
