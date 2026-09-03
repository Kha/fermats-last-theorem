import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator
attribute [-instance] FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing
attribute [-simp] AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator
    {K : Type*} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a b : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (gR gC gRd gCd : Multiset ℂ) (s : ℂ)
    (hconv : (rsDatum ℚ S a b c gR gC gRd gCd).Converges)
    (hs : (rsDatum ℚ S a b c gR gC gRd gCd).abscissa < (s + 1 / 2).re)
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hint : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
          (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)))
    (ψ : ∀ p : HeightOneSpectrum (𝓞 ℚ), AddChar (p.adicCompletion ℚ) ℂ)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (I : HeightOneSpectrum (𝓞 ℚ) → Type*) [∀ p, Fintype (I p)] [∀ p, Nonempty (I p)]
    (bc : ∀ p : HeightOneSpectrum (𝓞 ℚ), I p → p.adicCompletionIntegers ℚ)
    (hI : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → Fintype.card (I p) = Ideal.absNorm p.asIdeal)
    (om : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → b p = (Ideal.absNorm p.asIdeal : ℂ) * om p)
    (hψ0 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ r : p.adicCompletionIntegers ℚ,
      ψ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) = 1)
    (hψ1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∃ r : p.adicCompletionIntegers ℚ,
      ψ p (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
        algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) ≠ 1)
    (hN : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (placeEmbed ℚ p (unipotent x) * g) = ψ p x * W g)
    (hWK : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
      ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → W (g * placeEmbed ℚ p x) = W g)
    (hT : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ i, W (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (bc p i))))) +
        W (g * placeEmbed ℚ p (repInf
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp))) = a p * W g)
    (hZ : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      W (g * placeEmbed ℚ p (scalarPi
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp))) = om p * W g)
    (h : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℂ)
    (hh0 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → h p 0 = 1)
    (hh1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → h p 1 = inducedE1 ℚ c p)
    (hh2 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → h p 2 = inducedE1 ℚ c p ^ 2 - inducedE2 ℚ c p)
    (hh : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ n : ℕ, h p (n + 3) =
      inducedE1 ℚ c p * h p (n + 2) - inducedE2 ℚ c p * h p (n + 1) + inducedE3 ℚ c p * h p n)
    (u : HeightOneSpectrum (𝓞 ℚ) → ℕ → ℕ → ℂ)
    (hu0 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ k : ℕ, u p k 0 = h p k)
    (hu : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ k₁ k₂ : ℕ,
      u p k₁ (k₂ + 1) = h p k₁ * h p (k₂ + 1) - h p (k₁ + 1) * h p k₂)
    (uZ : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℤ → ℂ)
    (huZ_off : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ p m₁ m₂ = 0)
    (huZ_cone : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ p k₁ k₂ = u p k₁ k₂)
    (hFK : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
      ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → F (g * placeEmbed ℚ p x) = F g)
    (hF : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ),
      localAt ℚ p g = 1 →
        F (g * placeEmbed ℚ p
            (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp) (m₁ - m₂) *
              scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp) ^ m₂)) =
          F g * ((Ideal.absNorm p.asIdeal : ℂ)⁻¹ ^ m₁ * uZ p m₁ m₂)) :
    RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
      (rsDatum ℚ S a b c gR gC gRd gCd).LFun (s + 1 / 2) *
        RSCarrier.rsFinIntegral μ μN s
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g))
          ({g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsFinIntegral_eq_LFun_rsDatum_mul_rsFinIntegral_indicator.solution
