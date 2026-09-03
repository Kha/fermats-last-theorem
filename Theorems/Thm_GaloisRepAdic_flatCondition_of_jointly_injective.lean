import Mathlib.RingTheory.Artinian.Ring
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_flatCondition_of_jointly_injective
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem GaloisRepAdic.flatCondition_of_jointly_injective
    {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 P] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} {S : Finset ℕ}
    (hA : GaloisRep.flatCondition 𝒪 p S (ρ.baseChangeAlong πA hπA))
    (hB : GaloisRep.flatCondition 𝒪 p S (ρ.baseChangeAlong πB hπB)) :
    GaloisRep.flatCondition 𝒪 p S ρ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_flatCondition_of_jointly_injective.solution
