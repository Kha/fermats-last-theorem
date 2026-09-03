import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRep_ordinaryCondition_of_injective

theorem GaloisRep.ordinaryCondition_of_injective
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ) (ρ : GaloisRepAdic A)
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnB : IsNilpotent (p : B))
    (h : GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ)) :
    GaloisRep.ordinaryCondition 𝒪 p S ρ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_ordinaryCondition_of_injective.solution
