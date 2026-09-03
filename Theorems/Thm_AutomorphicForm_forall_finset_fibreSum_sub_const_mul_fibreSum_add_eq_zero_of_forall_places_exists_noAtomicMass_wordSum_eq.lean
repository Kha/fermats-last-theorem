import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_AutomorphicForm_forall_finset_fibreSum_sub_const_mul_fibreSum_add_eq_zero_of_forall_places_exists_noAtomicMass_wordSum_eq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_finset_fibreSum_sub_const_mul_fibreSum_add_eq_zero_of_forall_places_exists_noAtomicMass_wordSum_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hXrel : ∀ y ∈ X, ∀ w : HeightOneSpectrum (𝓞 L),
      conj (y w).1 = conj (y w).2 / ((‖(y w).2‖ : ℝ) : ℂ) * (y w).1)
    (hXfin : ∀ w : HeightOneSpectrum (𝓞 L), ((fun y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ => (y w).2) '' X).Finite)
    (CL : Set (HeckeEigensystem L ℂ)) (mL : HeckeEigensystem L ℂ → ℂ)
    (hmL : Summable fun Ψ : CL => ‖mL Ψ‖)
    (hXL : ∀ Ψ ∈ CL, mL Ψ ≠ 0 → (fun w : HeightOneSpectrum (𝓞 L) => (Ψ.a w, Ψ.b w)) ∈ X)
    {ΞT : Type} (Ξ : Finset ΞT) (CK : ΞT → Set (HeckeEigensystem K ℂ)) (mK : ΞT → HeckeEigensystem K ℂ → ℂ)
    (hmK : ∀ ξ ∈ Ξ, Summable fun π : CK ξ => ‖mK ξ π‖)
    (hXK : ∀ ξ ∈ Ξ, ∀ π ∈ CK ξ, mK ξ π ≠ 0 →
      (fun w : HeightOneSpectrum (𝓞 L) => ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w)) ∈ X)
    (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hEX : ∀ n, E n ∈ X) (e : ℕ → ℂ)
    (he : Summable fun n => ‖e n‖)
    (rec : ℕ → HeightOneSpectrum (𝓞 L)) (hrec : ∀ k, rec k ∉ SL)
    (hrecK : ∀ k, HeightOneSpectrum.under (𝓞 K) (rec k) ∉ SK)
    (hinj : Function.Injective fun k => HeightOneSpectrum.under (𝓞 K) (rec k))
    (t : HeightOneSpectrum (𝓞 L) → ℂ × ℂ)
    (bandL bandK c₀ : ℂ)
    (hword :
      ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
        (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
        ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
          (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
          (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
        ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
        (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
          ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
            ∀ g : C(X, ℂ),
              (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
              (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
        ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (g : C(X, ℂ)),
          (∀ x : X, g x = ∏ v ∈ T,
            ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
              ((HeckeEigensystem.cNorm (w' v))⁻¹ *
                ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
          bandL *
              (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL},
                (∏ v ∈ T, (Ψ.1.a (w' v)) ^ ks v * ((HeckeEigensystem.cNorm (w' v))⁻¹ * Ψ.1.b (w' v)) ^ js v) *
                  mL Ψ.1) -
            c₀ * bandK *
              (∑ ξK ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξK},
                (∏ v ∈ T, ((formalBaseChange K L π.1).a (w' v)) ^ ks v *
                    ((HeckeEigensystem.cNorm (w' v))⁻¹ * (formalBaseChange K L π.1).b (w' v)) ^ js v) *
                  mK ξK π.1) +
            (∑' n, e n * g ⟨E n, hEX n⟩) = Λ g) :
    ∀ F : Finset ℕ, 2 ≤ F.card →
      bandL * (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ CL ∧ ∀ k ∈ F, (Ψ.a (rec k), Ψ.b (rec k)) = t (rec k)}, mL Ψ.1) -
        c₀ * bandK * (∑ ξ ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ CK ξ ∧
            ∀ k ∈ F, ((formalBaseChange K L π).a (rec k), (formalBaseChange K L π).b (rec k)) = t (rec k)},
          mK ξ π.1) +
        (∑' n : {n : ℕ // ∀ k ∈ F, E n (rec k) = t (rec k)}, e n.1) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_forall_finset_fibreSum_sub_const_mul_fibreSum_add_eq_zero_of_forall_places_exists_noAtomicMass_wordSum_eq.solution
