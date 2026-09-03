import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K)) (k j : ℕ)
    (c : GL (Fin 2) (v.adicCompletion K))
    (hc : ∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
      (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (y : GL (Fin 2) (v.adicCompletion K)) :
    (∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (c * y))) =
      ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * y) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul.solution
