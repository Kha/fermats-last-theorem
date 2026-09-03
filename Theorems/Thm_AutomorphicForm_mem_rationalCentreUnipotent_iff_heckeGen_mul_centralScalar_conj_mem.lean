import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (y : AdelicGL2 (𝓞 K) K) :
    y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem.solution
