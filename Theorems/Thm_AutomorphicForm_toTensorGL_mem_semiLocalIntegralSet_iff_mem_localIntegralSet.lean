import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (s : GL (Fin 2) (v.adicCompletion K)) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K) s ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      s ∈ AutomorphicForm.localIntegralSet K v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet.solution
