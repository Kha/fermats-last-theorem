import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_AddSubgroup_inZeroComponentAt_of_cyclic_stable_scalar_dichotomy

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ m : ℕ) : ℤ))
      = p ^ (2 * m))
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hKstab : ∀ x ∈ K, σ • x ∈ K)
    {c : ZMod p} (hc1 : c ≠ 1) (hc1' : c ≠ -1)
    (hscal : ∀ x ∈ K, p • x = 0 → σ • x = c.val • x)
    (hDich : ∀ x ∈ K, ¬ W.InZeroComponentAt A x →
      W.InZeroComponentAt A (σ • x - x) ∨ W.InZeroComponentAt A (σ • x + x))
    (hZeroSub : ∀ x y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → p ^ m • y = 0 →
      W.InZeroComponentAt A x → W.InZeroComponentAt A y → W.InZeroComponentAt A (x - y))
    (hM : Nat.card
      {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
        p • x = 0 ∧ W.InZeroComponentAt A x} = p) :
    (∀ x ∈ K, W.InZeroComponentAt A x) ∧
      ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_inZeroComponentAt_of_cyclic_stable_scalar_dichotomy.solution
