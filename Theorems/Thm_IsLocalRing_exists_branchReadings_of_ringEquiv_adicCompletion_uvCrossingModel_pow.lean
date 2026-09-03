import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow

set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve ModularCurve.UVCrossingModel~exists_ringEquiv_quotient_span_V_powerSeries~mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne"

theorem IsLocalRing.exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (E : ℕ) (hE : 1 ≤ E)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ E))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ E) π)
    (cx cy : O) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hcx : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cx) = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hcy : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cy) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E))
    (PV PU : Ideal O) [PV.IsPrime] [PU.IsPrime]
    (htV : t ∈ PV) (hcyV : cy ∈ PV) (hcxV : cx ∉ PV)
    (htU : t ∈ PU) (hcxU : cx ∈ PU) (hcyU : cy ∉ PU) :

    (∀ f : O, f ∈ PV ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) ∧
    (∀ f : O, f ∈ PU ↔
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) ∧

    (∃ φV : O →+* PowerSeries (ResidueField W),
      (∀ f : O, φV f = 0 ↔ f ∈ PV) ∧
      (∀ f : O, f ∈ maximalIdeal O → PowerSeries.constantCoeff (φV f) = 0) ∧
      (∃ u : PowerSeries (ResidueField W), IsUnit u ∧ φV cx = u * PowerSeries.X) ∧
      (∀ (f : O) (n : ℕ), φV f ≠ 0 → (φV f).order = n →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) - γ * U (π ^ E) ^ n ∈
            Ideal.span {const (π ^ E) π, V (π ^ E)})) ∧

    (∃ φU : O →+* PowerSeries (ResidueField W),
      (∀ f : O, φU f = 0 ↔ f ∈ PU) ∧
      (∀ f : O, f ∈ maximalIdeal O → PowerSeries.constantCoeff (φU f) = 0) ∧
      (∃ u : PowerSeries (ResidueField W), IsUnit u ∧ φU cy = u * PowerSeries.X) ∧
      (∀ (f : O) (n : ℕ), φU f ≠ 0 → (φU f).order = n →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) - γ * V (π ^ E) ^ n ∈
            Ideal.span {const (π ^ E) π, U (π ^ E)})) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow.solution
