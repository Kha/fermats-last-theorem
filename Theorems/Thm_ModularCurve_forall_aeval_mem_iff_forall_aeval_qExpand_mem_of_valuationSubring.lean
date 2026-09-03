import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (j' : ↥K) (hj' : ((j' : LaurentSeries L)) = ModularCurve.qExpand L q ((j : ↥K) : LaurentSeries L))
    (V : ValuationSubring ↥K)
    (hA : ∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ V)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ V.nonunits) :
    (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j (P.map (algebraMap A L)))⁻¹ ∈ V) ↔
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j' (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j' (P.map (algebraMap A L)))⁻¹ ∈ V) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring.solution
