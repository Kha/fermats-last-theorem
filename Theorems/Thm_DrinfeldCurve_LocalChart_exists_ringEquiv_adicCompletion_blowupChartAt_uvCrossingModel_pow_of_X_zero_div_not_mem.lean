import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
attribute [-instance] instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem DrinfeldCurve.LocalChart.exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (ε : Oˣ) (hϖπ : ϖ = π ^ m * (ε : O))
    (ϖq : O) (hϖq : ϖq = ϖ ^ (q + 1))
    (f u v : MvPowerSeries (Fin 2) O) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q O ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O), MvPowerSeries.X 1}) ^ (q + 2))
    (hqO : (q : O) ∈ maximalIdeal O)
    (s : MvPowerSeries (Fin 2) O ⧸ Ideal.span {MvPowerSeries.C ϖq * v - f * u})
    (hsnz : s ∈ nonZeroDivisors (MvPowerSeries (Fin 2) O ⧸ Ideal.span {MvPowerSeries.C ϖq * v - f * u}))
    (hs : s ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u}) (MvPowerSeries.C ϖ),
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u}) (MvPowerSeries.X 0),
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u}) (MvPowerSeries.X 1)}) :
    let S := (MvPowerSeries (Fin 2) O ⧸ Ideal.span {MvPowerSeries.C ϖq * v - f * u})
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u})
    let 𝔐 : Ideal S := Ideal.span {mkS (MvPowerSeries.C ϖ), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}
    let Ls := Localization.Away s
    let Rs : Subring Ls := Subring.closure
      (Set.range (algebraMap S Ls) ∪ {x : Ls | ∃ i ∈ 𝔐, x * algebraMap S Ls s = algebraMap S Ls i})
    ∀ (P' : Ideal ↥Rs) (hP' : P'.IsMaximal)

      (hover : ∀ (i : S) (hi : algebraMap S Ls i ∈ Rs),
        i ∈ Ideal.span {mkS (MvPowerSeries.C π), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} → (⟨_, hi⟩ : ↥Rs) ∈ P')

      (hoff : ∀ (x : Ls) (hx : x ∈ Rs), x * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) → (⟨x, hx⟩ : ↥Rs) ∈ P'),
      ∀ (n : ℕ)
        (hchart : ∀ (t : Ls) (ht : t ∈ Rs), t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 0)) → (⟨t, ht⟩ : ↥Rs) ∉ P')
        (hslope : ∀ (t t' : Ls) (ht : t ∈ Rs) (ht' : t' ∈ Rs),
          t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 0)) →
          t' * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 1)) →
          (⟨t', ht'⟩ : ↥Rs) - ((n : ℕ) : ↥Rs) * ⟨t, ht⟩ ∈ P'),
    ∃ (hSR : ∀ i : S, algebraMap S Ls i ∈ Rs)
      (ι : AdicCompletion P' ↥Rs ≃+* UVCrossingModel O (π ^ m)),

      (∀ o : O, ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR (mkS (MvPowerSeries.C o))⟩) = const (π ^ m) o) ∧

      (∃ (p₀ p₁ : O) (α β : UVCrossingModel O (π ^ m)),
        (p₀ ∉ maximalIdeal O ∨ p₁ ∉ maximalIdeal O) ∧ (p₀ ^ q * p₁ - p₀ * p₁ ^ q ∈ maximalIdeal O) ∧
        ¬ IsUnit (α - const (π ^ m) p₀) ∧ ¬ IsUnit (β - const (π ^ m) p₁) ∧
        ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR (mkS (MvPowerSeries.X 0))⟩) = V (π ^ m) * α ∧
        ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR (mkS (MvPowerSeries.X 1))⟩) = V (π ^ m) * β) ∧

      (∃ γV : (UVCrossingModel O (π ^ m))ˣ,
        ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR s⟩) = (γV : UVCrossingModel O (π ^ m)) * V (π ^ m)) ∧
      (∀ (x : Ls) (hx : x ∈ Rs), x * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) →
        ∃ γU : (UVCrossingModel O (π ^ m))ˣ,
          ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨x, hx⟩) = (γU : UVCrossingModel O (π ^ m)) * U (π ^ m))  := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem.solution
