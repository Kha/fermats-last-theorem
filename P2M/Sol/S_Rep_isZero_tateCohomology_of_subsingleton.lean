import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
namespace P2MW.S_Rep_isZero_tateCohomology_of_subsingleton

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] [Subsingleton G]
    (A : Rep.{u} k G) (q : ℤ) : CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  classical

  have hnorm : ∀ v : A, A.ρ.norm v = v := by
    intro v
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single (1 : G) (fun g _ hg => absurd (Subsingleton.elim g 1) hg) (fun h => absurd (Finset.mem_univ _) h),
      map_one, Module.End.one_apply]
  rcases q with (_ | n) | (_ | n)
  ·
    show CategoryTheory.Limits.IsZero (ModuleCat.of k A.tateH0)
    haveI : Subsingleton A.tateH0 := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [Submodule.Quotient.eq]
      refine ⟨Representation.Coinvariants.mk _ ((x : A) - y), ?_⟩
      apply Subtype.ext
      rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, hnorm, Submodule.coe_sub]
    exact ModuleCat.isZero_of_subsingleton _
  · exact isZero_groupCohomology_succ_of_subsingleton A n
  ·
    show CategoryTheory.Limits.IsZero (ModuleCat.of k A.tateHneg1)
    haveI : Subsingleton A.tateHneg1 := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have key : ∀ c : A.tateHneg1, (c : A.ρ.Coinvariants) = 0 := by
        intro c
        obtain ⟨x, hx⟩ := Representation.Coinvariants.mk_surjective _ (c : A.ρ.Coinvariants)
        have h0 := congrArg Subtype.val c.2
        rw [← hx, Representation.normBar_mk, Representation.coe_normToInvariants_apply, hnorm] at h0
        rw [← hx, show x = 0 from h0, map_zero]
      rw [key a, key b]
    exact ModuleCat.isZero_of_subsingleton _
  · exact isZero_groupHomology_succ_of_subsingleton A n
