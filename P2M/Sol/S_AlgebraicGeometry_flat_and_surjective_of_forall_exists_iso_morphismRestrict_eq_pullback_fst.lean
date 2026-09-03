import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace S1C
namespace TorsorFlat

theorem of_forall_exists_iso_morphismRestrict_eq_pullback_fst (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    {S D B G : Scheme.{u}} (g : G ⟶ S) (hg : P g) (b : B ⟶ S) (π : D ⟶ B)
    (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧
      ∃ e : (π ⁻¹ᵁ U : Scheme.{u}) ≅ pullback (U.ι ≫ b) g,
        e.hom ≫ pullback.fst (U.ι ≫ b) g = π ∣_ U) :
    P π := by
  choose U hpU e he using hloc

  have hU : iSup U = ⊤ := top_le_iff.mp fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hpU p⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun p => ?_

  rw [← he p, P.cancel_left_of_respectsIso]
  exact P.pullback_fst _ _ hg

end S1C.TorsorFlat

theorem solution
    {S D B G : Scheme.{u}} (g : G ⟶ S) [Flat g] [Surjective g] (b : B ⟶ S) (π : D ⟶ B)
    (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧
      ∃ e : (π ⁻¹ᵁ U : Scheme.{u}) ≅ pullback (U.ι ≫ b) g,
        e.hom ≫ pullback.fst (U.ι ≫ b) g = π ∣_ U) :
    Flat π ∧ Surjective π :=
  ⟨S1C.TorsorFlat.of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Flat g ‹_› b π hloc,
    S1C.TorsorFlat.of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Surjective g ‹_› b π hloc⟩
