import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped ENNReal Classical

theorem AutomorphicForm.sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (w : NumberField.InfinitePlace K) (c : (InfiniteAdeleRing K)ˣ) (x : L ⊗[K] InfiniteAdeleRing K) :
    (∀ w' : NumberField.InfinitePlace L, w'.comap (algebraMap K L) = w →
      ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L
          (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • x))‖ =
        ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L x)‖ /
          ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖) ∧
    (∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L
          (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • x))‖ ^ 2) =
      ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        (w'.mult : ℝ) * (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L x)‖ ^ 2) -
          2 * Real.log ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖)) ∧
    (∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w), w'.mult =
      Module.finrank K L * w.mult) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul.solution
