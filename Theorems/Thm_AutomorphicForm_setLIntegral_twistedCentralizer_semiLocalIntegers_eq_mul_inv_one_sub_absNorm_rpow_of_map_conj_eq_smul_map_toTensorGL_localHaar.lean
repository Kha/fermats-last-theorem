import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
attribute [-simp] LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ))
    (hτ : τ.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (c : ℝ≥0∞)
    (hy : letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
      letI := AutomorphicForm.localGLBorel K v
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
          y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ =
        c • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))
    (hU : τ (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = c)
    (a : ℝ) (N : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ≥0∞)
    (hN : ∀ (t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (s : (v.adicCompletion K)ˣ),
      Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        Units.map (Algebra.TensorProduct.includeRight :
          v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s →
      N t = ((‖(s : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ a)) :
    ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) |
        ∀ i j, ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈ AutomorphicForm.semiLocalIntegers K L v},
        N t ∂τ =
      c * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-a))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - a))⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_semiLocalIntegers_eq_mul_inv_one_sub_absNorm_rpow_of_map_conj_eq_smul_map_toTensorGL_localHaar.solution
