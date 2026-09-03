import Mathlib
import Theorems.Thm_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective HasRingHomProperty.descendsAlong IsLocalIso LocallyQuasiFinite QuasiCompact IsLocalIso.le_of_isZariskiLocalAtSource Scheme Flat flat_and_surjective_SpecMap_iff HasRingHomProperty" namespace LocallyQuasiFinite end AlgebraicGeometry.LocallyQuasiFinite
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.LocallyQuasiFinite" in
theorem AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact' :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong @LocallyQuasiFinite (@Surjective ⊓ @Flat)
    (fun {R S} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
    (fun {R S} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) ?_ ?_
    RingHom.QuasiFinite.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]

theorem solution :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact'
