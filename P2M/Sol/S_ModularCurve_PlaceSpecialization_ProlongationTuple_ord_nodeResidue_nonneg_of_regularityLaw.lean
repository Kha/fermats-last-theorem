import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_nodeResidue_nonneg_of_regularityLaw
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    ∀ g : ↥(R.nodeIntegersOver K w),
      0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) ∧ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) := by
  intro g
  obtain ⟨c, h1, h2⟩ := hreg.2 (g : ↥(modularFunctionFieldBar (N * q))) g.2.1.1 g.2.1.2.1
    (smulNodePair (arithFrobC q k N) w) (smulNodePair_mem_nodePairsOfPlaces _ hw)
    (fun V hV => R.ord_nonneg_of_mem_nodeIntegers g.2.1 hV)
  exact ⟨w.ord_nonneg_of_mem h1.mem, (arithFrobC q k N • w).ord_nonneg_of_mem h2.mem⟩
