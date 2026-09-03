import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C

theorem WeierstrassCurve.exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C {𝒪 : Type*} [CommRing 𝒪] {k : Type*} [Field k] [IsAlgClosed k] (π : 𝒪 →+* k) [IsLocalHom π] (hπ : Function.Surjective π) (W : WeierstrassCurve k) [W.IsElliptic] : ∃ (E : WeierstrassCurve (PowerSeries 𝒪)) (_ : E.IsElliptic), (∃ v : WeierstrassCurve.VariableChange k, v • E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) = W) ∧ PowerSeries.map π E.j ≠ PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_powerSeries_isElliptic_variableChange_smul_map_eq_and_map_j_ne_C.solution
