import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (V : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) V]
    (hint : ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → ↥(modularFunctionFieldBar (N * q)),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y =
                c • ((ProlongationTuple.atkinLehnerBar N q (b i) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))) :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) V) → ↥(modularFunctionFieldBar (N * q)))
      (hG₁ : ∀ i, G i ∈ R.R₁.integers) (hG₂ : ∀ i, G i ∈ R.R₂.integers),
      (∀ i, G i ∈ V) ∧
      LinearIndependent k (fun i =>
        ((R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional.solution
