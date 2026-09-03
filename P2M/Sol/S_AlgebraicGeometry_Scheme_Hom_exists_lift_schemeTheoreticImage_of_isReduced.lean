import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.le_ofIdeals_iff Scheme.Hom QuasiCompact Scheme.preimage_basicOpen Scheme Scheme.Hom.imageι Scheme.basicOpen_zero Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion IsReduced eq_zero_of_basicOpen_eq_bot IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.ker_apply Scheme.IdealSheafData.ofIdeals Scheme.IdealSheafData"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.le_ofIdeals_iff Hom Γ preimage_basicOpen Hom.imageι basicOpen_zero IdealSheafData.ker_subschemeι basicOpen Hom.ker_apply Opens IdealSheafData.ofIdeals IdealSheafData" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image app imageι ker preimage_basicOpen ker_apply" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.basicOpen_inter_closure_range_eq_empty {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (s : Γ(Y, U)) (hs : f.app U s = 0) :
    (Y.basicOpen s : Set Y) ∩ closure (Set.range f.base) = ∅ := by
  have hpre : f ⁻¹ᵁ Y.basicOpen s = ⊥ := by
    rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero]
  have hdisj : (Y.basicOpen s : Set Y) ∩ Set.range f.base = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false, not_and,
      not_exists]
    intro hy x hx
    have : x ∈ f ⁻¹ᵁ Y.basicOpen s := by
      change f.base x ∈ (Y.basicOpen s : Set Y); rw [hx]; exact hy
    rw [hpre] at this
    exact this

  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨hy, hyc⟩
  have hopen : IsOpen ((Y.basicOpen s : Set Y)) := (Y.basicOpen s).isOpen
  rw [mem_closure_iff] at hyc
  obtain ⟨z, hz1, hz2⟩ := hyc _ hopen hy
  have : z ∈ (Y.basicOpen s : Set Y) ∩ Set.range f.base := ⟨hz1, hz2⟩
  rw [hdisj] at this
  exact this

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.ker_le_ker_of_range_subset_closure {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (u : T ⟶ Y) [IsReduced T] (h : Set.range u.base ⊆ closure (Set.range f.base)) :
    f.ker ≤ u.ker := by
  change f.ker ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (u.app U).hom
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  rw [Scheme.Hom.ker_apply] at hs
  change u.app U s = 0
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen]
  ext1
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h1 : u.base t ∈ (Y.basicOpen s : Set Y) := ht
  have h2 : u.base t ∈ closure (Set.range f.base) := h ⟨t, rfl⟩
  have := Scheme.Hom.basicOpen_inter_closure_range_eq_empty f s hs
  exact (Set.eq_empty_iff_forall_notMem.mp this) (u.base t) ⟨h1, h2⟩

end AlgebraicGeometry

theorem solution
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (u : T ⟶ Y) [IsReduced T]
    (h : Set.range u.base ⊆ closure (Set.range f.base)) :
    ∃ v : T ⟶ f.image, v ≫ f.imageι = u := by
  refine ⟨IsClosedImmersion.lift f.imageι u ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.Hom.ker_le_ker_of_range_subset_closure f u h
