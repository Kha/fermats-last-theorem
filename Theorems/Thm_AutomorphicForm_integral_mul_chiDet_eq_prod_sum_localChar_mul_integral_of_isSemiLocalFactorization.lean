import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfact : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (ns v),
          (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
        else φS v))
    (η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hη : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((η z : ℂˣ) : ℂ)) :
    ∫ g, φ g * chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (∏ v ∈ T, ∑ ι : Fin (ks v) → Fin (ns v),
          ((NumberField.TateGlobal.localChar η (ws v).1
            (Matrix.GeneralLinearGroup.det ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)) : ℂˣ) : ℂ)) *
        ∫ g, {g : AdelicGL2 (𝓞 L) L |
              ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v}.indicator
            (fun g => φa (glArch (𝓞 L) L g) *
              ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L g))) g *
          chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization.solution
