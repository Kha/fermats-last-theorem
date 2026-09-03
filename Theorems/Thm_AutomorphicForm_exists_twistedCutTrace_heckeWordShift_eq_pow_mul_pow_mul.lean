import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_twistedCutTrace_heckeWordShift_eq_pow_mul_pow_mul

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped TensorProduct
open scoped Pointwise
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_twistedCutTrace_heckeWordShift_eq_pow_mul_pow_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hfact : IsSemiLocalFactorization K L S φ φa φf φS)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (harch : IsArchBiFinite L tysL φ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (hvSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (w : v.Extension (𝓞 L))
    (w' : HeightOneSpectrum (𝓞 L)) (hw' : w'.asIdeal = σ • w.1.asIdeal)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (k j : ℕ) :
    ∃ (φ' : AdelicGL2 (𝓞 L) L → ℂ) (hφ' : Continuous φ') (hφ'c : HasCompactSupport φ')
      (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (insert v S) φ' φa φf'
        (Function.update φS v fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          ∑ ι : Fin k → Fin n,
            (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
              ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
                ((List.ofFn fun m => rT (ι m)).prod * z ^ j)))⁻¹ * x)) ∧
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ' ∧
        IsArchBiFinite L tysL φ' ∧
        ∀ Ψ : HeckeEigensystem L ℂ,
          twistedCutTrace K L D σ
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ' hφ' hφ'c =
            Ψ.a w' ^ k * Ψ.toRawCentral.b w' ^ j *
              twistedCutTrace K L D σ
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_twistedCutTrace_heckeWordShift_eq_pow_mul_pow_mul.solution
