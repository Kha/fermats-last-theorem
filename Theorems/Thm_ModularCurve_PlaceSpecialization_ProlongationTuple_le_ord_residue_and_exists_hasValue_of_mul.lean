import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_ord_residue_and_exists_hasValue_of_mul
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.le_ord_residue_and_exists_hasValue_of_mul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (Wset : Finset (Place k ↥(modularFunctionFieldC k N))) (hRL : R.RegularityLaw Wset)
    (w : Place k ↥(modularFunctionFieldC k N)) (hwW : w ∈ Wset)
    (f t : ↥(modularFunctionFieldBar (N * q)))
    (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → 0 ≤ V.ord (f * t))
    (n₁ n₂ : ℤ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (πw : ↥(modularFunctionFieldC k N)) (hπ : w.ord πw = 1)
    (htw₁ : w.HasValue (πw ^ (-n₁) * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • πw) ^ (-n₂) * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    (R.residue₁ ⟨f, hf₁⟩ ≠ 0 → -n₁ ≤ w.ord (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) ∧
    (R.residue₂ ⟨f, hf₂⟩ ≠ 0 → -n₂ ≤ (arithFrobC q k N • w).ord (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) ∧
    ∃ c : k,
      w.HasValue (πw ^ n₁ * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) (l₂ * c) ∧
      (arithFrobC q k N • w).HasValue
        ((arithFrobC q k N • πw) ^ n₂ * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) (l₁ * c) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_ord_residue_and_exists_hasValue_of_mul.solution
