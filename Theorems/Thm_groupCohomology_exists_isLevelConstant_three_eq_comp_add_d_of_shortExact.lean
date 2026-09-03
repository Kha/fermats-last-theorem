import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isLevelConstant_three_eq_comp_add_d_of_shortExact

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_isLevelConstant_three_eq_comp_add_d_of_shortExact
    {k : Type} [CommRing k] {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
    {N' N N'' : Rep.{0} k G} (ι : N' ⟶ N) (π : N ⟶ N'')
    (hι : Function.Injective ι.hom) (hπ : Function.Surjective π.hom) (hex : Function.Exact ι.hom π.hom)
    (hsm : ∀ m : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : G, r s ∈ F.fixingSubgroup → N.ρ s m = m)
    (u : (Fin 3 → G) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0)
    (b'' : (Fin 2 → G) → N'')
    (hlcb : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b'' (g * s) = b'' g)
    (hπu : (fun g => π.hom (u g)) = ((inhomogeneousCochains N'').d 2 3).hom b'') :
    ∃ (u' : (Fin 3 → G) → N') (b : (Fin 2 → G) → N),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 3 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → u' (g * s) = u' g) ∧
      ((inhomogeneousCochains N').d 3 4).hom u' = 0 ∧
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → b (g * s) = b g) ∧
      u = (fun g => ι.hom (u' g)) + ((inhomogeneousCochains N).d 2 3).hom b := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isLevelConstant_three_eq_comp_add_d_of_shortExact.solution
