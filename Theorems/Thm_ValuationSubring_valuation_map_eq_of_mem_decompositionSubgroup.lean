import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup (A : ValuationSubring (AlgebraicClosure ℚ)) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.decompositionSubgroup ℚ) (z : AlgebraicClosure ℚ) : A.valuation (σ z) = A.valuation z := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup.solution
