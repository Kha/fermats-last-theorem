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
import P2M.Sol.S_AutomorphicForm_exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem
    {Kc : Type*} [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [T2Space Kc]
    [SecondCountableTopology Kc] [MeasurableSpace Kc] [BorelSpace Kc]
    (μ : Measure Kc) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure]
    (E : Submodule ℂ (Kc → ℂ)) [FiniteDimensional ℂ E]
    (hEc : ∀ v ∈ E, Continuous v)
    (hEr : ∀ k : Kc, ∀ v ∈ E, (fun x => v (x * k)) ∈ E)
    (hEl : ∀ k : Kc, ∀ v ∈ E, (fun x => v (k * x)) ∈ E)
    (hEs : ∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ E) :
    ∃ e : Kc → ℂ, Continuous e ∧ (fun k => e k⁻¹) ∈ E ∧
      (∀ k : Kc, e k⁻¹ = conj (e k)) ∧
      (∀ k : Kc, ∫ k', e k' * e (k'⁻¹ * k) ∂μ = e k) ∧
      (∀ v ∈ E, ∀ x : Kc, ∫ k, e k * v (x * k) ∂μ = v x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem.solution
