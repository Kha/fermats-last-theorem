import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
namespace P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JHNeronObjectAtP.LevelData p M H hpM A) :
    ∃ ρ : baseRing p →+* ↥A, A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ) ∧ Λ.σA = Spec.map (CommRingCat.ofHom ρ) := by
  refine ⟨(Spec.preimage Λ.σA).hom, ?_, ?_⟩
  · have h := Λ.hσA
    rw [← Spec.map_preimage Λ.σA] at h
    change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (Spec.preimage Λ.σA) =
      Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ))) at h
    rw [← Spec.map_comp] at h
    have h2 := Spec.map_injective h
    have h3 := congrArg CommRingCat.Hom.hom h2
    simpa using h3
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
