import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_seedDatum_of_nodeCoordinates_nodeEquation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (us : ∀ w : ↥W, ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N))))
    (hus : ∀ w : ↥W, IsUnit (us w))
    (hxy : ∀ w : ↥W, (cs w).x * (cs w).y =
      R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N))
        ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Ks w))) ^ e (w : Place k (modularFunctionFieldC k N)) * us w) :
    ∃ (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)))
      (n : Place k (modularFunctionFieldC k N) → ℕ),
      (∀ (w) (hw : w ∈ W), y w = ((cs ⟨w, hw⟩).y : ↥(modularFunctionFieldBar (N * q)))) ∧
      (∀ w ∈ W, n w = W.lcm e / e w) ∧
      (∀ w ∈ W, y w ∈ R.nodeIntegers w) ∧
      (∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0) ∧
      (∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w → V.ord (y w) = 0) ∧
      (∀ w ∈ W, ∀ w' ∈ W,
        ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation.solution
