import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (W : Set (AdelicGL2 (𝓞 K) K)) (tysK : ArchTypeFamily K)
    (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ u : HeightOneSpectrum (𝓞 K), GL (Fin 2) (u.adicCompletion K) → ℂ)
    (hfact : IsUnitFactorization K S' f fa ff fS)
    (hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) f)
    (harch : IsArchBiFinite K tysK f)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') (hvS : v ∉ SK) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ) :
    ∃ (f'' : AdelicGL2 (𝓞 K) K → ℂ) (hf'' : Continuous f'') (hf''c : HasCompactSupport f'')
      (ff'' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsUnitFactorization K (insert v S') f'' fa ff''
          (Function.update fS v fun x => ∑ ι : Fin k → Fin n,
            (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * x)) ∧
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) f'' ∧
        IsArchBiFinite K tysK f'' ∧
        ∀ π : HeckeEigensystem K ℂ,
          cutTrace K
              (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f'' hf'' hf''c =
            π.a v ^ k * π.toRawCentral.b v ^ j *
              cutTrace K
                (productionPinsOf K W
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f hf hfc := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isUnitFactorization_insert_and_cutTrace_eq_pow_mul_cutTrace.solution
