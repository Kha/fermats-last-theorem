import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_detIsCyclotomic_of_jointly_injective

theorem GaloisRepAdic.detIsCyclotomic_of_jointly_injective {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ}
    (hnA : IsNilpotent (p : A)) (hnB : IsNilpotent (p : B))
    (hA : (ρ.baseChangeAlong πA hπA).DetIsCyclotomic p)
    (hB : (ρ.baseChangeAlong πB hπB).DetIsCyclotomic p) : ρ.DetIsCyclotomic p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_detIsCyclotomic_of_jointly_injective.solution
