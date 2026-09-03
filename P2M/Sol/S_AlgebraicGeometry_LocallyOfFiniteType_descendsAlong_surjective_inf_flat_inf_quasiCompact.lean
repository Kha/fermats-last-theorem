import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_LocallyOfFiniteType_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry"

theorem solution :
    DescendsAlong (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong (P := @LocallyOfFiniteType) (P' := @Surjective ⊓ @Flat)
    (Q := fun f => f.FiniteType) (Q' := fun f => f.FaithfullyFlat)
    (H₁ := ?_) (H₂ := ?_) RingHom.FiniteType.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro R S f hf
    exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩
