import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_MvPowerSeries_exists_X_pow_mem_span_of_X_pow_mem_span_map_of_surjective_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (φ : Series R) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hd : 0 < d)
    (h : FormalODModule.HasKernelOfDegree (φ.map π) d) :
    FormalODModule.HasKernelOfDegree φ d := by
  classical
  haveI : IsNoetherianRing S := isNoetherianRing_of_surjective R S π hπ
  have ccπ : ∀ i, MvPowerSeries.constantCoeff ((φ.map π) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map π (φ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hφ0 i, map_zero]

  obtain ⟨N, hN⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree (φ.map π) ccπ h
  obtain ⟨N', hN'⟩ := MvPowerSeries.exists_X_pow_mem_span_of_X_pow_mem_span_map_of_surjective_of_isNilpotent π hπ hker (σ := Fin 2) (ι := Fin 2) φ ⟨N, fun s => hN s⟩
  obtain ⟨hfin, hproj⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem φ hφ0 ⟨N', hN'⟩
  refine ⟨hfin, hproj, ?_⟩

  intro κ _ f
  obtain ⟨M, hM⟩ := hker
  have hle : RingHom.ker π ≤ RingHom.ker f := by
    intro x hx
    rw [RingHom.mem_ker]
    have hxM : x ^ M = 0 := by
      have : x ^ M ∈ RingHom.ker π ^ M := Ideal.pow_mem_pow hx M
      rw [hM] at this
      exact (Submodule.mem_bot _).mp this
    have : f x ^ M = 0 := by rw [← map_pow, hxM, map_zero]
    exact IsNilpotent.eq_zero ⟨M, this⟩
  let e := RingHom.quotientKerEquivOfSurjective hπ
  let fbar : S →+* κ := (Ideal.Quotient.lift (RingHom.ker π) f fun x hx => hle hx).comp e.symm.toRingHom
  have hf : fbar.comp π = f := by
    ext r
    show Ideal.Quotient.lift (RingHom.ker π) f (fun x hx => hle hx) (e.symm (π r)) = f r
    have : e.symm (π r) = Ideal.Quotient.mk (RingHom.ker π) r := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk]
  rw [← hf, ← Series.map_map]
  exact h.2.2 κ fbar

#print axioms solution
