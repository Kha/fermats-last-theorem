import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_iDeg_nine_identities_of_prime
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false
open CohCarrier in

theorem CohCarrier.jDeg_iDeg_nine_identities_of_prime (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_iDeg_nine_identities_of_prime.solution
