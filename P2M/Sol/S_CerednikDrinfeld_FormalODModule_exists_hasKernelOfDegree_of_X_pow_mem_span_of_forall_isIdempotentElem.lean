import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_forall_isIdempotentElem
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B]
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ d : ℕ, FormalODModule.HasKernelOfDegree φ d := by
  classical
  obtain ⟨hfin, hproj⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem φ hφ0 hN
  haveI := hfin
  haveI := hproj
  haveI : Module.Flat B (FormalODModule.KerAlgebra φ) := Module.Flat.of_projective
  haveI : Module.FinitePresentation B (FormalODModule.KerAlgebra φ) :=
    Module.finitePresentation_of_projective B (FormalODModule.KerAlgebra φ)

  haveI : PreconnectedSpace (PrimeSpectrum B) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases hconn e he with h | h
    · left
      rw [h, PrimeSpectrum.basicOpen_zero]
      rfl
    · right
      rw [h, PrimeSpectrum.basicOpen_one]
      rfl
  have hlc := Module.isLocallyConstant_rankAtStalk (R := B) (M := FormalODModule.KerAlgebra φ)
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨0, hfin, hproj, ?_⟩
    intro κ _ f
    exfalso
    have : (1 : κ) = 0 := by rw [← map_one f, ← map_zero f, Subsingleton.elim (1 : B) 0]
    exact one_ne_zero this
  · obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum B) := inferInstance
    refine ⟨Module.rankAtStalk (FormalODModule.KerAlgebra φ) p₀, hfin, hproj, ?_⟩
    intro κ _ f
    letI : Algebra B κ := f.toAlgebra
    obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ) φ hN
    have hfr : Module.finrank κ (FormalODModule.KerAlgebra (φ.map f)) =
        Module.finrank κ (κ ⊗[B] FormalODModule.KerAlgebra φ) :=
      (e.toLinearEquiv.finrank_eq).symm
    let q : PrimeSpectrum κ := ⟨⊥, Ideal.bot_prime⟩
    have h1 : Module.rankAtStalk (κ ⊗[B] FormalODModule.KerAlgebra φ) q =
        Module.finrank κ (κ ⊗[B] FormalODModule.KerAlgebra φ) := by
      rw [Module.rankAtStalk_eq_finrank_of_free]
      rfl
    have h3 := Module.rankAtStalk_baseChange (R := B) (M := FormalODModule.KerAlgebra φ) (S := κ) q
    rw [hfr, ← h1, h3]
    exact hlc.apply_eq_of_preconnectedSpace _ _
