import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_AutomorphicForm_IwasawaShellIndex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ rationalCentreUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    iwasawaShellIndex K v (x * g) = iwasawaShellIndex K v g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent.solution
