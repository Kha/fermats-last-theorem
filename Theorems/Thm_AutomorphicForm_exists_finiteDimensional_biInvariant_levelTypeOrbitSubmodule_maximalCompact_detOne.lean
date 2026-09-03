import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicLevel~conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact NumberField.AdelicBox NumberField.AdelicHaar"
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ E ∧
      (∀ v ∈ E, Continuous fun k : ↥(adelicMaximalCompact K) => v (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 K) K, v x ≠ 0 → x ∈ adelicMaximalCompact K ∧ (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K x) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1)) ∧
      (∀ k ∈ adelicMaximalCompact K, (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ v ∈ E, (fun x => v (k * x)) ∈ E ∧ (fun x => v (x * k)) ∈ E) ∧
      (∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ E) ∧
      (∀ v ∈ E, ∃ S : Finset (AdelicGL2 (𝓞 K) K → ℂ),
        (∀ s ∈ S, Continuous fun k : ↥(adelicMaximalCompact K) => s (k : AdelicGL2 (𝓞 K) K)) ∧
        ∀ k ∈ adelicMaximalCompact K,
          (fun x => v (k * x)) ∈ Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 K) K → ℂ))) ∧
      (∀ v ∈ E, ∀ (x : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        v (x * u) = v x) ∧
      E ≤ archCutSubmodule K tysK ∧
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        ∀ x : AdelicGL2 (𝓞 K) K, ∃ v ∈ E, ∀ k ∈ adelicMaximalCompact K, (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
          v k = φ (x * k)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne.solution
