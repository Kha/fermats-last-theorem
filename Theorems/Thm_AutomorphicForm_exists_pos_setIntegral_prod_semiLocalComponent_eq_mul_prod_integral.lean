import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μf : @Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (glBorelOf (FiniteAdeleRing (𝓞 L) L)))
    (hμf : @Measure.IsHaarMeasure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) _ _
      (glBorelOf (FiniteAdeleRing (𝓞 L) L)) μf)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ F : (v : HeightOneSpectrum (𝓞 K)) → (GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        (∀ v ∈ S, Continuous (F v) ∧ HasCompactSupport (F v)) →
        ∫ h in {h | ∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v},
            ∏ v ∈ S, F v (semiLocalComponent K L v h) ∂μf =
          (c : ℂ) * ∏ v ∈ S, ∫ t, F v t ∂(semiLocalHaar K L v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral.solution
