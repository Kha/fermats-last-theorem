module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import Definitions.Def_ModularCurve_LevelOneProlongationPair
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint

@[expose] public section

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.NodeLocalized IsLocalRing
theorem ModularCurve.NodeLocalized.exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (x y : A)
    (hx : 0 < W.ord (PlaceSpecialization.jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)))
    (hy : 0 < W.ord (PlaceSpecialization.jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) A.toSubring red (red x) (red y)) :
    ∃ a : A, g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)
      ∈ W.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint.solution
