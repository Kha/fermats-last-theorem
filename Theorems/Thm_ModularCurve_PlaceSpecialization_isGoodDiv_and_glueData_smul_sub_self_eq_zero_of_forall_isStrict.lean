import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          (∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
            P.IsGoodDiv (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict.solution
