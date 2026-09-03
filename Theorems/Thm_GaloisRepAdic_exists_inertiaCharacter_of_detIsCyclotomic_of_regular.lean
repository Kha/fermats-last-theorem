import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_inertiaCharacter_of_detIsCyclotomic_of_regular

set_option autoImplicit false
open IsLocalRing Polynomial
theorem GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (ρ : GaloisRepAdic R) {p : ℕ} (hp : p.Prime) (hdet : ρ.DetIsCyclotomic p) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) (hpq : p ∣ q - 1) (hunr : ρ.residual.IsUnramifiedAt q)
    (hreg : ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∀ (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), P.IsFrobeniusAt φ q →
        ∃ α β : ResidueField R, α ≠ β ∧ LinearMap.charpoly (ρ.residual.ρ φ) = (X - C α) * (X - C β))
    {k : ℕ} (hk : ¬ p ^ (k + 1) ∣ q - 1)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k))) (hπΔ : Function.Surjective πΔ) :
    ∃ χ : Multiplicative (ZMod (p ^ k)) →* Rˣ,
      ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
        ∃ b : Module.Basis (Fin 2) R ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ρ.ρ σ (b 0) = ((χ (πΔ (cyc σ)) : Rˣ) : R) • b 0 ∧
          ρ.ρ σ (b 1) = (((χ (πΔ (cyc σ)))⁻¹ : Rˣ) : R) • b 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_inertiaCharacter_of_detIsCyclotomic_of_regular.solution
