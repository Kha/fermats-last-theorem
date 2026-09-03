import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_ordinaryCondition_baseChangeAlong

theorem GaloisRepAdic.ordinaryCondition_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ) :
    GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_ordinaryCondition_baseChangeAlong.solution
