import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem AddSubgroup.mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (m : ℕ)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (he : p • e = 0)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (p : ℤ)) = p ^ 2)
    (hZeroSub : ∀ x y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → p ^ m • y = 0 →
      W.InZeroComponentAt A x → W.InZeroComponentAt A y → W.InZeroComponentAt A (x - y))
    (hStep3 : ∀ k ∈ K, ¬ W.InZeroComponentAt A (e - k)) :
    ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub.solution
