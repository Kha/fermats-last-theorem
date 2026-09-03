import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_tubeEquation_smul_sub_self_of_annulus
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (w : Place k (modularFunctionFieldC k N))
    (An : Annulus A ↥(modularFunctionFieldBar (N * q)))
    (hdom : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V' ∈ An.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hmod : ((An.modulus : AlgebraicClosure ℚ) ≠ 0))
    (hσZ : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • An.param = An.param)
    (hZ₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((An.modulus : AlgebraicClosure ℚ))⁻¹
        * An.param ∈ R.R₁.integers)
    (hZ₂ : An.param ∈ R.R₂.integers)
    (hZ₂0 : R.residue₂ ⟨An.param, hZ₂⟩ ≠ 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : V ∈ An.dom) :
    ∃ (x : A) (u : (↥A)ˣ) (t : ↥(modularFunctionFieldBar (N * q))) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
      x ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, x * d = An.modulus) ∧
      σ (x : AlgebraicClosure ℚ) = ((u : A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) ∧
      V.HasValue An.param (x : AlgebraicClosure ℚ) ∧
      t = (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (σ (x : AlgebraicClosure ℚ)))
          * (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))⁻¹ ∧
      (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)) ∧
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) = 1 ∧
      ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
        V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus.solution
