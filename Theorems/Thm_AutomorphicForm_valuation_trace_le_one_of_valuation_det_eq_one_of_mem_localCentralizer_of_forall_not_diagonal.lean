import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (m : GL (Fin 2) (v.adicCompletion K)) (hm : m ∈ AutomorphicForm.localCentralizer K v γ₀)
    (hdet : Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1) :
    Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal.solution
