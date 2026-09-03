import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
namespace P2MW.S_Rep_exact_tateDelta0_map

universe u

set_option autoImplicit false
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδ₀ hX) ((groupCohomology.functor k G 1).map X.f).hom := by
  have h1 : LinearMap.range (groupCohomology.δ hX 0 1 rfl).hom =
      LinearMap.ker (groupCohomology.map (MonoidHom.id G) X.f 1).hom :=
    (groupCohomology.mapShortComplex₁_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
  intro x
  change (groupCohomology.map (MonoidHom.id G) X.f 1).hom x = 0 ↔ _
  rw [← LinearMap.mem_ker, ← h1]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨Submodule.Quotient.mk ((groupCohomology.H0Iso X.X₃).hom w), ?_⟩
    rw [Rep.tateδ₀_mk]
    congr 1
    exact CategoryTheory.Iso.hom_inv_id_apply _ _
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨(groupCohomology.H0Iso X.X₃).inv z, (Rep.tateδ₀_mk hX z).symm⟩
