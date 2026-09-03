import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong

theorem GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsStrictOrdinaryAt p) : (ρ.baseChangeAlong φ hφ).IsStrictOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong.solution
