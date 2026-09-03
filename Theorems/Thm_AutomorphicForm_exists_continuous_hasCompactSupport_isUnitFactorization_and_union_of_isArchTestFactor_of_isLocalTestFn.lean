import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ SK, IsLocalTestFn K v (fSK v)) :
    ∃ (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      Continuous f₀ ∧ HasCompactSupport f₀ ∧ IsUnitFactorization K SK f₀ faK ff₀ fSK ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T SK →
        IsUnitFactorization K (SK ∪ T) f₀ faK ff₀
          (fun v => if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn.solution
