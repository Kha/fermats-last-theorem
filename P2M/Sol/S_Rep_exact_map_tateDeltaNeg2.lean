import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import P2M.Util
namespace P2MW.S_Rep_exact_map_tateDeltaNeg2

universe u

set_option autoImplicit false
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact ((groupHomology.functor k G 1).map X.g).hom (Rep.tateδneg2 hX) := by
  have h3 : LinearMap.range (groupHomology.map (MonoidHom.id G) X.g 1).hom =
      LinearMap.ker (groupHomology.δ hX 1 0 rfl).hom :=
    (groupHomology.mapShortComplex₃_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
  intro z
  rw [Subtype.ext_iff, Rep.coe_tateδneg2_apply]
  change (groupHomology.H0Iso X.X₁).hom ((groupHomology.δ hX 1 0 rfl) z) = 0 ↔
    z ∈ Set.range (groupHomology.map (MonoidHom.id G) X.g 1).hom
  constructor
  · intro hz
    have hz' : (groupHomology.δ hX 1 0 rfl) z = 0 := by
      have h := congrArg (groupHomology.H0Iso X.X₁).inv hz
      rw [CategoryTheory.Iso.hom_inv_id_apply] at h
      exact h.trans (LinearMap.map_zero _)
    have : z ∈ LinearMap.range (groupHomology.map (MonoidHom.id G) X.g 1).hom := by
      rw [h3]; exact hz'
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have : (groupHomology.map (MonoidHom.id G) X.g 1).hom y ∈ LinearMap.ker (groupHomology.δ hX 1 0 rfl).hom := by
      rw [← h3]; exact LinearMap.mem_range_self _ _
    rw [LinearMap.mem_ker] at this
    change (groupHomology.H0Iso X.X₁).hom ((groupHomology.δ hX 1 0 rfl).hom ((groupHomology.map (MonoidHom.id G) X.g 1).hom y)) = 0
    rw [this]
    exact LinearMap.map_zero _
