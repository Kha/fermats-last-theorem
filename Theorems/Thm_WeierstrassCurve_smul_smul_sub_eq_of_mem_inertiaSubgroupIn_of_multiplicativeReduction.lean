import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ)
    (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {n : ℕ} (hn : ¬ q ∣ n) {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : n • P = 0) :
    τ • (σ • P - P) = σ • P - P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction.solution
