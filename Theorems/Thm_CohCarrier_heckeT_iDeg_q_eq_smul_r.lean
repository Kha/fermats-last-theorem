import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_iDeg_q_eq_smul_r

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_q_eq_smul_r {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (r : ℕ) (hrN : r ∣ N) (hr : 4 ≤ r)
    (Hr : Subgroup (ZMod N)ˣ)
    (hHr : ∀ u : (ZMod N)ˣ, u ∈ Hr ↔ ZMod.castHom hrN (ZMod r) (u : ZMod N) = 1)
    (Hr' : Subgroup (ZMod (N * q))ˣ)
    (hHr' : ∀ u : (ZMod (N * q))ˣ,
      u ∈ Hr' ↔ ZMod.castHom (dvd_mul_of_dvd_left hrN (q)) (ZMod r) (u : ZMod (N * q)) = 1)
    (h₁ : LevelLE N (N * q) Hr Hr' 1)
    (hq : LevelLE N (N * q) Hr Hr' q)
    (φ : H1 N Hr A) :
    heckeT (N * q) Hr' q A (iDeg' N (N * q) Hr Hr' q A hq φ)
      = q • iDeg' N (N * q) Hr Hr' 1 A h₁ φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_iDeg_q_eq_smul_r.solution
