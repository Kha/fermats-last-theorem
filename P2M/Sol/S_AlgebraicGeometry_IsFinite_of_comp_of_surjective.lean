import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsFinite_of_comp_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsFinite (f ≫ g)] [LocallyOfFiniteType g] [IsSeparated g] : IsFinite g := by
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  haveI : IsProper g := IsProper.mk
  haveI : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    have hfin := (f ≫ g).finite_preimage_singleton z
    have hsub : g.base ⁻¹' {z} ⊆ f.base '' ((f ≫ g).base ⁻¹' {z}) := by
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, by simpa [Scheme.Hom.comp_apply] using hy, rfl⟩
    exact (hfin.image _).subset hsub
  exact IsFinite.of_isProper_of_locallyQuasiFinite g
