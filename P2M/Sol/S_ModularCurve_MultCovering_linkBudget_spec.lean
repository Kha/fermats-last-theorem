import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ModularCurve_MultCovering_exists_linkBudget
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_linkBudget_spec
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ i j, (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j ∈ A :=
  Nat.sInf_mem (ModularCurve.MultCovering.exists_linkBudget Φ s hs) A hA
