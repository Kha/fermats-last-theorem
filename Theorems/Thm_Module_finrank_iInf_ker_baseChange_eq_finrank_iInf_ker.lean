import Mathlib
import P2M.Util
import P2M.Sol.S_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker

open scoped TensorProduct

theorem Module.finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
    (F : Type) [Field F] (K : Type) [Field K] [Algebra F K]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ι : Type} (T : ι → (V →ₗ[F] V)) :
    Module.finrank K ↥(⨅ i, LinearMap.ker ((T i).baseChange K)) =
      Module.finrank F ↥(⨅ i, LinearMap.ker (T i)) := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker.solution
