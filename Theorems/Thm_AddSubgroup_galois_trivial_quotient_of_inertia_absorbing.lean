import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem AddSubgroup.galois_trivial_quotient_of_inertia_absorbing
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hopen : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      ∀ x : Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ m : ℕ) : ℤ),
      σ • x = x})
    (hInert : ∀ ℓ : ℕ, ℓ.Prime →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → τ • y - y ∈ K) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → σ • y - y ∈ K := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing.solution
