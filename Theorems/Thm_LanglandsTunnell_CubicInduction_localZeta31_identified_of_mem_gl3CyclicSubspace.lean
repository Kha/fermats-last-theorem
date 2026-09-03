import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell LanglandsTunnell.Converse
p2m_open "NumberField.TateGlobal LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe MeasureTheory"
open LanglandsTunnell.TateLocal

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.localZeta31_identified_of_mem_gl3CyclicSubspace
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (q : HeightOneSpectrum (𝓞 ℚ))
    (W₃ : LocalGL3 q → ℂ) (lam : ℂ)
    (hId :
      ∀ b : ℕ,
        (∀ w ∈ primeFibre ℚ K q,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : (q.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ q η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA q = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 q,
              letI := LanglandsTunnell.TateLocal.localBorel ℚ q
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove q
                  (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                  W₃ η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 q
                      (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                      W₃ η s g *
                    Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove q
                  (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) (dualWhittakerFn3 W₃) η⁻¹
                  (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 q
                      (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                      (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) W₃ η (1 - s) g *
                    Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lam *
                      (∏ᶠ w ∈ primeFibre ℚ K q,
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ primeFibre ℚ K q,
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))
    (W : LocalGL3 q → ℂ) (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ b : ℕ,
      (∀ w ∈ primeFibre ℚ K q,
        2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
          LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
      ∀ (η : (q.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ q η cη → cη ≤ b →
        ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
          NumberField.TateGlobal.localChar ηA q = η →
          LanglandsTunnell.Converse.IsAdmissibleTwist K
            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
          ∀ g : LocalGL3 q,
            letI := LanglandsTunnell.TateLocal.localBorel ℚ q
            ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
              IsLocalZeta30ConvergentAbove q
                (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                W η g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 q
                    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                    W η s g *
                  Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
              IsLocalZeta31ConvergentAbove q
                (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) (dualWhittakerFn3 W) η⁻¹
                (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 q
                    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) W η (1 - s) g *
                  Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                  (lam *
                    (∏ᶠ w ∈ primeFibre ℚ K q,
                      ((NumberField.TateGlobal.localChar
                        (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                    (∏ᶠ w ∈ primeFibre ℚ K q,
                      (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                          (NumberField.TateGlobal.localChar
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                        (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                          (LanglandsTunnell.Converse.pinnedExp K
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace.solution
