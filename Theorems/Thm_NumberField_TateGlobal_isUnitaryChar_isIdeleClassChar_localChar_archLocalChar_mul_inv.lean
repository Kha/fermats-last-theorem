import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_inv

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem NumberField.TateGlobal.isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_inv
    (K : Type) [Field K] [NumberField K]
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμu : AutomorphicForm.IsUnitaryChar (𝓞 K) K μ) (hνu : AutomorphicForm.IsUnitaryChar (𝓞 K) K ν)
    (hμF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (hνF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K ν)
    (hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (μ * ν⁻¹) ∧
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (μ * ν⁻¹) ∧
    (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν⁻¹) z : ℂˣ) : ℂ)) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      localChar (μ * ν⁻¹) v u = localChar μ v u * (localChar ν v u)⁻¹) ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      IsUnramifiedCharAt μ v → IsUnramifiedCharAt ν v → IsUnramifiedCharAt (μ * ν⁻¹) v) ∧
    (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      archLocalChar (μ * ν⁻¹) v x = archLocalChar μ v x * (archLocalChar ν v x)⁻¹) ∧
    (∀ τμ τν : InfinitePlace K → ℝ,
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v : ℝ) : ℂ) * Complex.I)) →
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τν v : ℝ) : ℂ) * Complex.I)) →
      ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v - τν v : ℝ) : ℂ) * Complex.I)) ∧
    (∀ mμ mν : InfinitePlace K → ℤ,
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v)) →
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v)) →
      ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v - mν v)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_inv.solution
