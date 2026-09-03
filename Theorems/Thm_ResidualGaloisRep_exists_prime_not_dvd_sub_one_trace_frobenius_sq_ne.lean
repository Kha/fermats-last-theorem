import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

set_option autoImplicit false

open Polynomial IsLocalRing

theorem ResidualGaloisRep.exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (Sram : Finset ℕ) (hram : ∀ q : ℕ, q.Prime → q ∉ Sram → ρbar.IsUnramifiedAt q)
    (T : Finset ℕ) :
    ∃ r : ℕ, r.Prime ∧ r ∉ T ∧ ¬ p ∣ r - 1 ∧ ρbar.IsUnramifiedAt r ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : k) + 1) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_prime_not_dvd_sub_one_trace_frobenius_sq_ne.solution
