import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization MazurRapoportAppendix
open scoped BigOperators

set_option maxHeartbeats 400000 in
open Classical in

theorem ModularCurve.PlaceSpecialization.sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
    (q N : ℕ) [Fact q.Prime] [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ (P.reduceFst V' ∈ W ∧ 0 < depth V' ∧ depth V' < e (P.reduceFst V')))
    (hstrict : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      ¬ (P.IsStrictFst V' ∧ P.IsStrictSnd V') ∧ (P.reduceFst V' ∈ W → ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))

    {node : Type} [Fintype node] [DecidableEq node] (wd : node → ℕ)
    (σN : ↥W ≃ node) (hσN : ∀ w : ↥W, wd (σN w) = e (w : Place k (modularFunctionFieldC k N)))

    {m : ℕ} (pos neg : Fin m → ℕ) (v : Fin m → X0MqComponents wd) (swap : Bool)
    (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support))
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hdict : ∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W then
           DRResolvedModelPackage.chainPos wd (σN ⟨_, hw⟩)
             (if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
         else Sum.inl 0))

    (Φ : X0MqComponents (widthOfPlaces (arithFrobC q k N) W e) ≃ X0MqComponents wd)
    (hΦ0 : Φ (Sum.inl 0) = if swap then Sum.inl 1 else Sum.inl 0)
    (hΦ1 : Φ (Sum.inl 1) = if swap then Sum.inl 0 else Sum.inl 1)
    (hΦr : ∀ (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) (kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1)) (kk' : Fin (wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) - 1)),
      (if swap then kk.val + kk'.val + 2 = wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) else kk'.val = kk.val) →
        Φ (Sum.inr ⟨s, kk⟩) = Sum.inr ⟨σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s), kk'⟩) :
    (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
      (∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) *
          (∑ j, if v j = Φ (Sum.inr ⟨s, kk⟩) then ((pos j : ℤ) - (neg j : ℤ)) else 0)) =
        P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
          ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1)) ∧
    ((∑ j, if v j = Φ (Sum.inl 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) =
      Divisor.degree (P.sndDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level.solution
