import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (ℓ : ℕ) [NeZero ℓ]
    {dataᵣ : ModularPolynomialData q} {hKrᵣ : KroneckerCongruence q dataᵣ}
    {hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {Pᵣ : PlaceSpecialization A q (N * ℓ) dataᵣ hKrᵣ k red hαᵣ hβᵣ} (Rᵣ : ProlongationTuple Pᵣ)
    (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) :
    ∃ h' : towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
        (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q) f ∈ Rᵣ.R₁.integers,
      ((Rᵣ.residue₁ ⟨_, h'⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
        = qExpand k ℓ ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq.solution
