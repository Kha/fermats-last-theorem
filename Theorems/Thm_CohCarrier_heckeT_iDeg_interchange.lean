import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_iDeg_interchange

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_interchange {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT (N * q) ⊤ q A (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
      = iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ)
          - iDeg' N (N * q) ⊤ ⊤ q A hq φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_iDeg_interchange.solution
