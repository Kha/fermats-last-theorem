import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsFinIntegral_eq_inv_eval_rsEulerPoly_mul_rsFinIntegral_indicator
attribute [-instance] FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing
attribute [-simp] AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.rsFinIntegral_eq_inv_eval_rsEulerPoly_mul_rsFinIntegral_indicator
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (lam om : ℂ)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers ℚ)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hψ0 : ∀ r : v.adicCompletionIntegers ℚ,
      ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers ℚ,
      ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hWK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hT : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ i, W (g * placeEmbed ℚ v (repSome
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i))))) +
        W (g * placeEmbed ℚ v (repInf
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      W (g * placeEmbed ℚ v (scalarPi
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = om * W g)
    (e₁ e₂ e₃ : ℂ) (h : ℕ → ℂ) (hh0 : h 0 = 1) (hh1 : h 1 = e₁) (hh2 : h 2 = e₁ ^ 2 - e₂)
    (hh : ∀ n : ℕ, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (u : ℕ → ℕ → ℂ) (hu0 : ∀ k : ℕ, u k 0 = h k)
    (hu : ∀ k₁ k₂ : ℕ, u k₁ (k₂ + 1) = h k₁ * h (k₂ + 1) - h (k₁ + 1) * h k₂)
    (uZ : ℤ → ℤ → ℂ) (huZ_off : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0)
    (huZ_cone : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = u k₁ k₂)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hFK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hF : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ), localAt ℚ v g = 1 →
      F (g * placeEmbed ℚ v
          (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m₁ - m₂) *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m₂)) =
        F g * ((Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ m₁ * uZ m₁ m₂))
    (hint : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
          (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) :
    RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
      ((rsEulerPoly lam ((Ideal.absNorm v.asIdeal : ℂ) * om) e₁ e₂ e₃).eval
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))))⁻¹ *
        RSCarrier.rsFinIntegral μ μN s
          ({g : finiteAdelicGL2Subgroup ℚ |
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g))
          ({g : finiteAdelicGL2Subgroup ℚ |
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsFinIntegral_eq_inv_eval_rsEulerPoly_mul_rsFinIntegral_indicator.solution
