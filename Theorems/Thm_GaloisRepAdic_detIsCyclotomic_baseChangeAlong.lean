import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_detIsCyclotomic_baseChangeAlong

theorem GaloisRepAdic.detIsCyclotomic_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.DetIsCyclotomic p) : (ρ.baseChangeAlong φ hφ).DetIsCyclotomic p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_detIsCyclotomic_baseChangeAlong.solution
