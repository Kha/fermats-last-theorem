import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero

set_option autoImplicit false

p2m_open "MeasureTheory NumberField IsDedekindDomain AutomorphicForm~exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent"
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (w : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (w.adicCompletion K)] [BorelSpace (w.adicCompletion K)]
    (μ : Measure (ι → w.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ {a : ι → w.adicCompletion K | ¬ ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k} = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero.solution
