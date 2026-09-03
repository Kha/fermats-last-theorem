import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology~continuousH2SrInflation_H2pi_eq_of_le~exists_continuousH2SrInflation_eq~continuousH2SrInflation_H2pi_eq_zero_iff"

theorem groupCohomology.exists_continuousH2SrInflation_eq_of_nsmul_eq_zero
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (n : ℕ) (z : continuousH2Sr r S M) (hz : n • z = 0) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) (_ : IsGalois ℚ F)
      (y : H2 (M.quotientToInvariants (F.fixingSubgroup.comap r))),
      n • y = 0 ∧ continuousH2SrInflation r S M F hF y = z := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero.solution
