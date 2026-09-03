import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isOrdinaryAt_of_jointly_injective

theorem GaloisRepAdic.isOrdinaryAt_of_jointly_injective {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdetA : (ρ.baseChangeAlong πA hπA).DetIsCyclotomic p)
    (hA : (ρ.baseChangeAlong πA hπA).IsOrdinaryAt p)
    (hB : (ρ.baseChangeAlong πB hπB).IsOrdinaryAt p) : ρ.IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_jointly_injective.solution
