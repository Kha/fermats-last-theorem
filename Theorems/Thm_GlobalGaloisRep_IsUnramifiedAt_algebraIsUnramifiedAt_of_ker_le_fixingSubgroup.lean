import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import P2M.Util
import P2M.Sol.S_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup

theorem GlobalGaloisRep.IsUnramifiedAt.algebraIsUnramifiedAt_of_ker_le_fixingSubgroup
    {G : Type*} [Group G] {ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G} {q : ℕ}
    (hq : q.Prime) (hunr : GlobalGaloisRep.IsUnramifiedAt ρ q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : ρ.ker ≤ F.fixingSubgroup)
    (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal] (hqP : (q : NumberField.RingOfIntegers F) ∈ P) :
    Algebra.IsUnramifiedAt ℤ P := by p2m_exact_reverting @_root_.P2MW.S_GlobalGaloisRep_IsUnramifiedAt_algebraIsUnramifiedAt_of_ker_le_fixingSubgroup.solution
