import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal

set_option autoImplicit false
theorem ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
    (p : ℕ) [Fact p.Prime] :
    ((padicPlace p).decompositionSubgroup ℚ
        : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      ≤ (MonoidHom.range (localGaloisToGlobal p)).topologicalClosure := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal.solution
