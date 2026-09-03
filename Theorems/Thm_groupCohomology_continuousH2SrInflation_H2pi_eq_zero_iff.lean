import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) [Normal ℚ F]
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ f) = 0 ↔
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (G ⧸ F'.fixingSubgroup.comap r) → M.quotientToInvariants (F'.fixingSubgroup.comap r)),
      ∀ g h : G, ((f ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
        = M.ρ g (y (h : G ⧸ F'.fixingSubgroup.comap r)) - (y ((g * h : G) : G ⧸ F'.fixingSubgroup.comap r) : M) + y (g : G ⧸ F'.fixingSubgroup.comap r) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff.solution
