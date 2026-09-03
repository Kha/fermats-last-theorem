import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_MDivRepresents
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictFst
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictFst Q) (hQ' : P.IsStrictFst Q')
    (hQQ' : P.reduceFst Q' = P.reduceFst Q)
    (haff : IsAffineGeomPlace k N (P.reduceFst Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceFst Q) ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceFst Q) ∧
      ((P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        (P.reduceFst Q).ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hgen : (P.reduceFst Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jGeomGen k N) ∧
      (P.reduceFst Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jNGeomGen k N))
    (m' : ℕ) {n : ℕ} (f : Fin n → ↥(modularFunctionFieldBar (N * q))) (hfI : ∀ l, f l ∈ R.R₁.integers)
    (hfd : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.IsStrictFst V → P.reduceFst V = P.reduceFst Q →
      -((Finsupp.single Q' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V
          + (m' : ℤ) * ((Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V))
        ≤ V.ord (f l)) :
    ∃ (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w : Fin 2 → Fin (m' + 1) → A)
      (G : Fin 2 → MvPolynomial (Option (Fin 2)) A) (p s : Fin n → MvPolynomial (Option (Fin 2)) A)
      (σ : Fin n → Fin (m' + 1) → A),
      PlaceSpecialization.IsFstTriple (q := q) (P.reduceFst Q) (red u) z y₁ y₂ ∧
      (∀ j : Fin 2, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (G j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (G 0).vars ∧
      0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ∧
      (∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j 0 : AlgebraicClosure ℚ))) ∧
      0 < Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) ∧
      red τ = red u ∧
      (∀ l, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (p l) =
        f l * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ^ m' *
          (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) *
          PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (s l)) ∧
      (∀ l, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0)) (s l)) ≠ 0) ∧
      (∀ j : Fin 2, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0))
        (MvPolynomial.pderiv (some j) (G j))) ≠ 0) ∧
      (∀ (j : Fin 2) (r : Fin (m' + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0) ∧
      (∀ (l : Fin n) (r : Fin (m' + 1)),
        ((∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σ l r')) *
            MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (s l) - 1).coeff r = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictFst.solution
