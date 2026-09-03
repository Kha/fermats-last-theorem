import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K)
      (_hdet : ∀ w : InfinitePlace K,
        ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1),
    (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (fun x => ψf s (x * k))) ∧
    (∀ s, IsArchKFinite K (fun x => ψf s (x * k))) ∧
    (∀ s, IsKfSmooth K (fun x => ψf s (x * k))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 (p.2 * k)) ∧
    (∀ g, Differentiable ℂ (fun s => ψf s (g * k))) ∧
    (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k' : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k' : AdelicGL2 (𝓞 K) K) * k)) ∈ W) ∧
    (∀ (s : ℂ) (k' : adelicMaximalCompact K),
      ψf s ((k' : AdelicGL2 (𝓞 K) K) * k) = ψf 0 ((k' : AdelicGL2 (𝓞 K) K) * k)) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u * k) = ψf s (g * k)) ∧
    (∀ s : ℂ, (fun x => ψf s (x * k)) ∈ archCutSubmodule K tysK) ∧
    (∫ k', ‖ψf 0 ((k' : AdelicGL2 (𝓞 K) K) * k)‖ ^ 2 ∂(maximalCompactHaar K)
      = ∫ k', ‖ψf 0 (k' : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_rightTranslate_adelicMaximalCompact_det_one_isInducedSection_isArchKFinite_isKfSmooth_flat_principalLevel_archCutSubmodule_and_integral_norm_sq_eq.solution
