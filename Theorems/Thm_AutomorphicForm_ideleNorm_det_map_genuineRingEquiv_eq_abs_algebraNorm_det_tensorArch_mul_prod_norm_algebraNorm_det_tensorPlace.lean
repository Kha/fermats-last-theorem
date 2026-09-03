import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hg : ∀ v ∉ S, AutomorphicForm.tensorPlace K L v g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) g)) =
      |Algebra.norm ℝ (Matrix.det ((AutomorphicForm.tensorArch K L g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| *
        ∏ v ∈ S, ‖Algebra.norm (v.adicCompletion K)
          (Matrix.det ((AutomorphicForm.tensorPlace K L v g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace.solution
