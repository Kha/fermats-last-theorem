import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (ϖL : w.1.adicCompletionIntegers L) (hϖL : Irreducible ϖL)
    (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
    (UK : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hUK : UK = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
    (UL : Subgroup (GL (Fin 2) (w.1.adicCompletion L)))
    (hUL : UL = LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
    (TK EK : HeckePair.HeckeAlgebra UK ℂ)
    (hTK : (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator fun _ => (1 : ℂ))
    (hEK : (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) •
        ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ UK,
            (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
              algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator fun _ => (1 : ℂ)))
    (TL EL : HeckePair.HeckeAlgebra UL ℂ)
    (hTL : (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator fun _ => (1 : ℂ))
    (hEL : (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (Ideal.absNorm w.1.asIdeal : ℂ) •
        ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ UL,
            (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
              algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator fun _ => (1 : ℂ)))
    (p : ℕ → HeckePair.HeckeAlgebra UK ℂ) (hp0 : p 0 = 2) (hp1 : p 1 = TK)
    (hp : ∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) :
    ∃ b : HeckePair.HeckeAlgebra UL ℂ →ₐ[ℂ] HeckePair.HeckeAlgebra UK ℂ,
      b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
      ∀ φ : HeckePair.HeckeAlgebra UL ℂ,
        AreMatchingLocal K L v σ
          (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
              (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
          (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.solution
