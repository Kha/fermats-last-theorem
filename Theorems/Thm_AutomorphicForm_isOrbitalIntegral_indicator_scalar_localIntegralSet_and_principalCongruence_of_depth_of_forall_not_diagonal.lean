import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
attribute [-simp] LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions
theorem AutomorphicForm.isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))

    (γ : GL (Fin 2) (v.adicCompletion K)) (_hγT : γ ∈ AutomorphicForm.localCentralizer K v γ₀)
    (_hγreg : AutomorphicForm.IsRegularSemisimple γ)
    (_hdet : Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1)

    (m : ℕ) (a : v.adicCompletion K) (_ha : Valued.v a ≤ 1) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (_hY : ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + (ϖ ^ m) • Y)
    (_hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (_hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))

    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (_hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (_hτν : @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ = νT) :
    letI := AutomorphicForm.localGLBorel K v

    let q : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
    let f₀ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)
    let f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
          ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)
    let θ : ℝ := (νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal
    let Ram : Prop := ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)
    let Near : Prop := 1 ≤ m ∧ Valued.v (a - 1) < 1
    (Ram →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f₀ ((q ^ (m + 1) - 1) / ((q - 1) * (θ : ℂ))) ∧
      (Near → AutomorphicForm.IsOrbitalIntegral K v γ τ f₁ ((q ^ m - 1) / ((q - 1) * (θ : ℂ))))) ∧
    (¬ Ram →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f₀ (((q + 1) * q ^ m - 2) / ((q - 1) * (θ : ℂ))) ∧
      (Near → AutomorphicForm.IsOrbitalIntegral K v γ τ f₁ (((q + 1) * q ^ (m - 1) - 2) / ((q - 1) * (θ : ℂ))))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal.solution
