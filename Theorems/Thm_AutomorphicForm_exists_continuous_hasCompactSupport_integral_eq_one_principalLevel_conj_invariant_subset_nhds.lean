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
import P2M.Sol.S_AutomorphicForm_exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (U : Set (AdelicGL2 (𝓞 K) K)) (hU : U ∈ nhds (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, ((f x).re : ℂ) = f x ∧ 0 ≤ (f x).re) ∧
      (∫ x, f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1) ∧
      (∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ y : AdelicGL2 (𝓞 K) K, f (u * y) = f y) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) ∧
      (∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
        ∃ a u : AdelicGL2 (𝓞 K) K, a ∈ U ∧ glFin (𝓞 K) K a = 1 ∧
          u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * u) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_integral_eq_one_principalLevel_conj_invariant_subset_nhds.solution
