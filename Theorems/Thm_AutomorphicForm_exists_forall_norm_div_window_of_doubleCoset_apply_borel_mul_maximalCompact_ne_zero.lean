import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
attribute [-simp] AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∃ cS cinf : ℝ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∀ (b : AdelicGL2 (𝓞 L) L), b ∈ AutomorphicForm.adelicBorel (𝓞 L) L →
      ∀ (k : AdelicGL2 (𝓞 L) L), k ∈ AutomorphicForm.adelicMaximalCompact L →
      ∀ (z : (AdeleRing (𝓞 L) L)ˣ),
        φ ((b * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (b * k))) ≠ 0 →
      ∀ (A B E : AdeleRing (𝓞 L) L),
        ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = A →
        ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = B →
        ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = E →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T → ∀ w : v.Extension (𝓞 L),
            ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ = 1 ∧ ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ 1) ∧
        (∀ v ∈ T, ∀ w : v.Extension (𝓞 L),
            |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤
              A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ∧
            Real.posLog ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤
              A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) ∧
        (∀ v ∈ S, v ∉ T → ∀ w : v.Extension (𝓞 L),
            |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤ cS ∧ Real.posLog ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ cS) ∧
        (∀ w : NumberField.InfinitePlace L,
            |Real.log ‖((B.1 w : w.Completion) / (A.1 w : w.Completion))‖| ≤ cinf ∧ Real.posLog ‖((E.1 w : w.Completion) / (A.1 w : w.Completion))‖ ≤ cinf) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero.solution
