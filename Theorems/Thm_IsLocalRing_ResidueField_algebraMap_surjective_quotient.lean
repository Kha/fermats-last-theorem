import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_IsLocalRing_ResidueField_algebraMap_surjective_quotient

theorem IsLocalRing.ResidueField.algebraMap_surjective_quotient
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (h : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField A))) :
    Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField (A ⧸ I))) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_ResidueField_algebraMap_surjective_quotient.solution
