import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S) (a : Kˣ) :
    NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) *
      (∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a : K)‖) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (a : K)‖) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one.solution
