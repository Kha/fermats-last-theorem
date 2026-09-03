import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar

theorem NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace
    (K : Type) [Field K] [NumberField K]
    (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.solution
