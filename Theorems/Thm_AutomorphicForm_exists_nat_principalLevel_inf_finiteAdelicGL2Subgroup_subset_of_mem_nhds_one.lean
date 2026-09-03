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
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicLevel~exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one NumberField.AdelicBox NumberField.AdelicHaar"
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open Topology in

theorem AutomorphicForm.exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one
    (K : Type) [Field K] [NumberField K]
    (V : Set (AdelicGL2 (𝓞 K) K)) (_hV : V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ m : ℕ, ((principalLevel (𝓞 K) K (Ideal.span {((m + 1 : ℕ) : 𝓞 K)}) ⊓ finiteAdelicGL2Subgroup K :
        Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) ⊆ V := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one.solution
