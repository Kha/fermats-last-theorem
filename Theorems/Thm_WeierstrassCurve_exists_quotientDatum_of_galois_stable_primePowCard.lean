import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primePowCard

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem WeierstrassCurve.exists_quotientDatum_of_galois_stable_primePowCard
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime)
    (hQD1 : ∀ (V : WeierstrassCurve ℤ), V.Δ ≠ 0 →
      ∀ (L : AddSubgroup ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        Nat.card L = p →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ L, σ • x ∈ L) →
      ∃ (V' : WeierstrassCurve ℤ)
        (χ : ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
             ((V'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        V'.Δ ≠ 0 ∧ χ.ker = L ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
           (x : ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
          χ (σ • x) = σ • χ x) ∧
        (∀ q : ℕ, q.Prime → q ≠ p → (q : ℤ) ∣ V.Δ → ¬ (q : ℤ) ∣ V.c₄ →
          ((q : ℤ) ∣ V'.Δ ∧ ¬ (q : ℤ) ∣ V'.c₄ ∧
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
              ∀ y : ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
                (V'.InZeroComponentAt A (χ y) ↔
                  ∃ k ∈ L, V.InZeroComponentAt A (y - k)))))
    (m : ℕ)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (hKstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K) :
    ∃ (W' : WeierstrassCurve ℤ)
      (φ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
           ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      W'.Δ ≠ 0 ∧ φ.ker = K ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
         (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        φ (σ • x) = σ • φ x) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄ →
        ((q : ℤ) ∣ W'.Δ ∧ ¬ (q : ℤ) ∣ W'.c₄ ∧
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
            ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
              (W'.InZeroComponentAt A (φ y) ↔
                ∃ k ∈ K, W.InZeroComponentAt A (y - k)))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primePowCard.solution
