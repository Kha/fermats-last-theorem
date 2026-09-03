import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_comb_eq_zero

set_option autoImplicit false

theorem CohCarrier.heckeT_comb_eq_zero {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (h₁ : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    [NeZero (N * q * q)] (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (h₁' : LevelLE (N * q) (N * q * q) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q * q))ˣ) 1)
    (hq' : LevelLE (N * q) (N * q * q) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q * q))ˣ) q)
    (φ : H1 N ⊤ A) :
    heckeT (N * q * q) ⊤ q A
        (q • iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ)
          - iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ (heckeT N ⊤ q A φ))
          + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq φ)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_comb_eq_zero.solution
