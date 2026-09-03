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
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
    (K : Type) [Field K] [NumberField K]
    (C Cx Cy : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (hCx : IsCompact Cx) (hCy : IsCompact Cy)
    (γ : GL (Fin 2) K) :
    ∃ S : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact S ∧
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, (∃ x ∈ Cx, ∃ y ∈ Cy,
          x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
            (AutomorphicForm.centralScalar (𝓞 K) K z * y) ∈ C) → z ∈ S := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact.solution
