import Definitions.Def_AutomorphicForm_IwasawaShellIndex
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (iwasawaShellIndex K v) ∧ Measurable (iwasawaShellIndex K v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable.solution
