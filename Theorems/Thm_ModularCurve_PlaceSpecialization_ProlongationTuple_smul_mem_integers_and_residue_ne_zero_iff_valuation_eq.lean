import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_smul_mem_integers_and_residue_ne_zero_iff_valuation_eq
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.smul_mem_integers_and_residue_ne_zero_iff_valuation_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hR : R.IsModel)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (c₀ : AlgebraicClosure ℚ) (h₀ : c₀ • f ∈ R.R₁.integers) (hr₀ : R.R₁.residue ⟨c₀ • f, h₀⟩ ≠ 0)
    (c' : AlgebraicClosure ℚ) :
    ((∃ h : c' • f ∈ R.R₁.integers, R.R₁.residue ⟨c' • f, h⟩ ≠ 0) ↔ A.valuation c' = A.valuation c₀) ∧
    (∀ (d₀ : AlgebraicClosure ℚ) (hd₀ : d₀ • f ∈ R.R₂.integers), R.R₂.residue ⟨d₀ • f, hd₀⟩ ≠ 0 →
      ∀ d' : AlgebraicClosure ℚ,
        ((∃ h : d' • f ∈ R.R₂.integers, R.R₂.residue ⟨d' • f, h⟩ ≠ 0) ↔ A.valuation d' = A.valuation d₀)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_smul_mem_integers_and_residue_ne_zero_iff_valuation_eq.solution
