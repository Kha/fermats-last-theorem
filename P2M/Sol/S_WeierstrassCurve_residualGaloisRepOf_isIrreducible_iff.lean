import Definitions.Def_GaloisRep_Residual
import P2M.Util
namespace P2MW.S_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p)) :
    (W.residualGaloisRepOf p hcard hker).IsIrreducible ↔
      WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ W p := by
  have hp : p.Prime := Fact.out
  haveI hfin : Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.pos.ne')
  have hnt : Nontrivial (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hp.one_lt
  constructor
  · intro h
    exact ⟨hnt, h⟩
  · intro h
    exact h.2
