module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring

@[expose] public section
attribute [-instance] ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint
attribute [-simp] ModularCurve.NodeLocalized.coe_modularEvalAt
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
    IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
    ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = 2 ∧
    (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring.solution
