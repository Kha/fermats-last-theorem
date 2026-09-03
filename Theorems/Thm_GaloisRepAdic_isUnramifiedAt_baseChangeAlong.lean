import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isUnramifiedAt_baseChangeAlong

theorem GaloisRepAdic.isUnramifiedAt_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {q : ℕ} (h : ρ.IsUnramifiedAt q) : (ρ.baseChangeAlong φ hφ).IsUnramifiedAt q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isUnramifiedAt_baseChangeAlong.solution
