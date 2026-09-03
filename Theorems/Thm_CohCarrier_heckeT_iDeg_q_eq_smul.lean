import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_iDeg_q_eq_smul

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_q_eq_smul {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ q A hq φ)
      = q • iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul.solution
