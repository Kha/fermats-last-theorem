import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [NeZero n]
    (hnsq : ¬ IsSquare c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ (δ : AlgebraicClosure K), δ * δ = algebraMap K (AlgebraicClosure K) c ∧
      ∃ et : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n
          ≃ rootsOfUnity n (AlgebraicClosure K),
        (∀ P Q, et (P + Q) = et P * et Q) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (P : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n),
          (σ δ = δ →
            ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            = σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∧
          (σ δ = -δ →
            ((et (σ • P) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            * σ ((et P : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare.solution
