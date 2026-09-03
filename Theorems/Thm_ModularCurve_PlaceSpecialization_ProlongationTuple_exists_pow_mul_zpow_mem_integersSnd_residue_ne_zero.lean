import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (u : modularFunctionFieldBar (N * q)) (hu0 : u ≠ 0)
    (hu : ∀ h₂ : u ∈ R.R₂.integers, R.R₂.residue ⟨u, h₂⟩ = 0)
    (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
      ∃ h₂ : f ^ m * u ^ j ∈ R.R₂.integers, R.R₂.residue ⟨f ^ m * u ^ j, h₂⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero.solution
