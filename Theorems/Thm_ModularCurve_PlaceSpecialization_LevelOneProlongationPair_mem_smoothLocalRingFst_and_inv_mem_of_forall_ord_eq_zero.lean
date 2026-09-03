import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : ∃ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.IsStrictTypeOne W ∧ P.redFst W = v)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (h₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hdisc : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeOne W → P.redFst W = v → W.ord f = 0) :
    f ∈ R.smoothLocalRingFst v ∧ f⁻¹ ∈ R.smoothLocalRingFst v := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero.solution
