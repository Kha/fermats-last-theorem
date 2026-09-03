import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Descent
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective HasRingHomProperty.descendsAlong IsLocalIso QuasiCompact IsLocalIso.le_of_isZariskiLocalAtSource Scheme Smooth Flat Etale flat_and_surjective_SpecMap_iff HasRingHomProperty"
p2m_open "AlgebraicGeometry"

theorem desc_smooth_descendsAlong :
    DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong (P := @Smooth) (P' := @Surjective ⊓ @Flat)
    (Q := fun f => f.Smooth) (Q' := fun f => f.FaithfullyFlat)
    (H₁ := ?_) (H₂ := ?_) RingHom.Smooth.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro R S f hf
    exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩

end AlgebraicGeometry

open CategoryTheory _root_.CategoryTheory.MorphismProperty _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry in
theorem solution :
    DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  AlgebraicGeometry.desc_smooth_descendsAlong
