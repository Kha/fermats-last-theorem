import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant

theorem WeierstrassCurve.exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant {L : Type*} [Field L] (A : ValuationSubring L) (E₁ E₂ : WeierstrassCurve A) (h₁ : IsUnit E₁.Δ) (h₂ : IsUnit E₂.Δ) (C : WeierstrassCurve.VariableChange L) (hC : C • E₁.map A.subtype = E₂.map A.subtype) : ∃ C₀ : WeierstrassCurve.VariableChange A, C₀.map A.subtype = C ∧ C₀ • E₁ = E₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant.solution
