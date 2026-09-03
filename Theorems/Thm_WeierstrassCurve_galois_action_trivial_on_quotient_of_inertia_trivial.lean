import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.galois_action_trivial_on_quotient_of_inertia_trivial (W : WeierstrassCurve ℚ) {n : ℕ} [Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)] (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n, σ • x - x ∈ N) : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n, σ • x - x ∈ N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial.solution
