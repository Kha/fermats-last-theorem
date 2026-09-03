import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
namespace P2MW.S_FormalGroup_LawHom_appAdic_zero

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace QuotIsoAux

open Filter Topology

theorem eval₂_zero_eq {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
    {A : Type*} [CommRing A] [Algebra R₀ A] (I : Ideal A) [IsAdicComplete I A] (f : PowerSeries R₀) :
    (letI : WithIdeal A := ⟨I⟩; PowerSeries.eval₂ (algebraMap R₀ A) (0 : A) f) =
      algebraMap R₀ A (PowerSeries.constantCoeff f) := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have hsum := PowerSeries.hasSum_eval₂ hφ (PowerSeries.HasEval.zero) f
  refine hsum.unique ?_
  convert hasSum_single (f := fun d : ℕ => algebraMap R₀ A (PowerSeries.coeff d f) * (0 : A) ^ d) 0 ?_ using 1
  · simp
  · intro d hd
    simp [hd]

end QuotIsoAux

theorem solution
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {F G : FormalGroup R} (φ : FormalGroup.LawHom F G) :
    φ.appAdic I (0 : R) = 0 := by
  have h := @QuotIsoAux.eval₂_zero_eq R _ ⊥ inferInstance R _ _ I _ φ.series
  rw [φ.constantCoeff_series, map_zero] at h
  unfold FormalGroup.LawHom.appAdic FormalGroup.LawHom.app FormalGroup.evalSeries
  exact h
