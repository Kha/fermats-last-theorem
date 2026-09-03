import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (z : (AdeleRing (𝓞 K) K)ˣ) (hz : ((z : AdeleRing (𝓞 K) K)).1 = 1)
    (hzf : ∀ v : HeightOneSpectrum (𝓞 K),
      ((z : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ∧
      (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K) :
    χ z = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers.solution
