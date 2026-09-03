import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRep_strictOrdinaryCondition_of_jointly_injective

set_option autoImplicit false
theorem GaloisRep.strictOrdinaryCondition_of_jointly_injective
    {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 P] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hnA : IsNilpotent (p : A)) (hnB : IsNilpotent (p : B))
    (hA : GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong πA hπA))
    (hB : GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong πB hπB)) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_strictOrdinaryCondition_of_jointly_injective.solution
