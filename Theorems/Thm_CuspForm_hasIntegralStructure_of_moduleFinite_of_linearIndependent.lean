import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent
set_option autoImplicit false

theorem CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent (N : ℕ) [NeZero N] (k : ℤ) (hk : 1 ≤ k)
    (hfin : Module.Finite ℤ (CuspForm.heckeAlgebra N k (∅ : Set ℕ)))
    (hind : ∀ {ι : Type} (T : ι → CuspForm.heckeAlgebra N k (∅ : Set ℕ)), LinearIndependent ℤ T →
      LinearIndependent ℂ
        (fun i => ((T i : CuspForm.heckeAlgebra N k (∅ : Set ℕ)) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)))) :
    CuspForm.HasIntegralStructure N k := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent.solution
