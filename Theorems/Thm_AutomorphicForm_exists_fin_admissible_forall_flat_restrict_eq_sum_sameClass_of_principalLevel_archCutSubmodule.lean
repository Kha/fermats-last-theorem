import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
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
import P2M.Sol.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions
attribute [-simp] NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    let Adm : (∀ x, 0 < ((αm x : ℝˣ) : ℝ)) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        (ℂ → AdelicGL2 (𝓞 K) K → ℂ) → Prop := fun hαm μ ν ψf =>
      IsUnitaryChar (𝓞 K) K μ ∧ IsUnitaryChar (𝓞 K) K ν ∧
      IsIdeleClassChar (𝓞 K) K μ ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)) ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s)) ∧
      (∀ s, IsArchKFinite K (ψf s)) ∧
      (∀ s, IsKfSmooth K (ψf s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => ψf s g)) ∧
      (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
      (∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g) ∧
      (∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
    let SameClass : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → Prop := fun μ' ν' μ ν =>
      ∀ (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ adelicBorel (𝓞 K) K), g ∈ adelicMaximalCompact K →
        ((μ (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ) =
          ((μ' (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν' (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ)
    ∃ (n : ℕ) (μs νs : Fin n → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) (ψs : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (i : Fin n), Adm hαm (μs i) (νs i) (ψs i)) ∧
      (∀ i j : Fin n, Integrable (fun k : adelicMaximalCompact K =>
        ψs i 0 (k : AdelicGL2 (𝓞 K) K) * conj (ψs j 0 (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
      (∀ a : Fin n → ℂ,
        (∫ k, ‖∑ j, a j * ψs j 0 ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) = 0 →
          a = 0) ∧
      ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ),
        Adm hαm μ ν ψf →
        ∃ a : Fin n → ℂ,
          (∀ k : adelicMaximalCompact K,
            ψf 0 (k : AdelicGL2 (𝓞 K) K) = ∑ i, a i * ψs i 0 (k : AdelicGL2 (𝓞 K) K)) ∧
          (∀ i, a i ≠ 0 → SameClass (μs i) (νs i) μ ν) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule.solution
