import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem NumberField.TateGlobal.localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (hχ : IsUnramifiedCharAt χ v)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    localChar χ v ϖ = χ (uniformizerIdele K v) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt.solution
