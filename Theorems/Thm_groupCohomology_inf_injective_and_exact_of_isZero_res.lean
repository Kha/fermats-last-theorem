import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_inf_injective_and_exact_of_isZero_res

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology Rep
theorem groupCohomology.inf_injective_and_exact_of_isZero_res
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (q : ℕ)
    (hvan : ∀ i : ℕ, 1 ≤ i → i < q → CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype A) i)) :
    Function.Injective (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) q).hom ∧
    ∀ x : groupCohomology A q, (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) q).hom x = 0 →
      ∃ y : groupCohomology (A.quotientToInvariants S) q,
        (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) q).hom y = x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inf_injective_and_exact_of_isZero_res.solution
