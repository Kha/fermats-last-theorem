import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_AddSubgroup_eq_atP_filtration_of_cyclic_stable_inertia_nontrivial

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem AddSubgroup.eq_atP_filtration_of_cyclic_stable_inertia_nontrivial
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ℕ) (hm : 1 ≤ m)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (hKstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ K, σ • x ∈ K)
    (hNontriv : ∃ τ ∈ A.inertiaSubgroupIn ℚ, ∃ x ∈ K, p • x = 0 ∧ τ • x ≠ x)
    (F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hFabs : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → σ • y - y ∈ F) :
    K ≤ F := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_eq_atP_filtration_of_cyclic_stable_inertia_nontrivial.solution
