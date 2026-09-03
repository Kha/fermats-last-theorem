import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd

set_option autoImplicit false

open CohCarrier in

theorem CohCarrier.jDeg_iDeg_four_identities_of_dvd (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hqN : q ∣ N)
    (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q) :
    (∀ φ, jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = q • φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = q • φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = heckeT N ⊤ q A φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = heckeTlower N ⊤ q A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd.solution
