import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

set_option autoImplicit false

open Polynomial

theorem ResidualGaloisRep.det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq
    {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] (ρbar : ResidualGaloisRep k)
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* k)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : k))
    (r : ℕ) (hr : r.Prime) (hrp : r ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime r)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ r) :
    LinearMap.det (ρbar.ρ σ) = (r : k) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq.solution
