import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_glArch_mul_glFin_heckeWord_of_not_mem

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.apply_mul_centralScalar_localUnit_eq_of_glArch_mul_glFin_heckeWord_of_not_mem
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K)))
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hϖKs0 : ∀ v ∈ T,
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (m : (u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hff : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ AutomorphicForm.localIntegralSet K v) →
        ff h = ∏ v ∈ SK ∪ T,
          (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
            else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h))
    (hff0 : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ AutomorphicForm.localIntegralSet K v) →
        ff h = 0)
    (hf : ∀ g, f g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
    (v₀ : HeightOneSpectrum (𝓞 K)) (hv₀ : v₀ ∉ SK)
    (t : (v₀.adicCompletion K)ˣ) (ht : Valued.v (t : v₀.adicCompletion K) = 1)
    (g : AdelicGL2 (𝓞 K) K) :
    f (g * AutomorphicForm.centralScalar (𝓞 K) K
      (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v₀ t))) = f g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_glArch_mul_glFin_heckeWord_of_not_mem.solution
