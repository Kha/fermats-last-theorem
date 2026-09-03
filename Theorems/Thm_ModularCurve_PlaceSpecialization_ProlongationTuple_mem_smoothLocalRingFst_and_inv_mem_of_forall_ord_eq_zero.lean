import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : P.ProlongationTuple)
    (v : Place k ↥(modularFunctionFieldC k N))
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hdisc : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst W → P.reduceFst W = v → W.ord f = 0) :
    f ∈ R.smoothLocalRingFst v ∧ f⁻¹ ∈ R.smoothLocalRingFst v := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_smoothLocalRingFst_and_inv_mem_of_forall_ord_eq_zero.solution
