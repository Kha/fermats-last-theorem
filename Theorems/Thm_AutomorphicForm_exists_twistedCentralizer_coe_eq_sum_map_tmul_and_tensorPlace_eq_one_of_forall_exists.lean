import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.cpowChar_apply_val AutomorphicForm.whittakerCoefficient_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain open AutomorphicForm hiding exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (β : ι → K) (hβ : ∑ k, β k • b k = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ι → AdeleRing (𝓞 K) K)
    (harch : ∀ k, (a k).1 = algebraMap K (InfiniteAdeleRing K) (β k))
    (hS : ∀ w ∈ S, ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] (a k).2 w)
    (hoff : ∀ k, ∀ w ∉ S, (a k).2 w = algebraMap K (w.adicCompletion K) (β k)) :
    ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ((t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
          (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k) ∧
      ∀ w ∉ S, AutomorphicForm.tensorPlace K L w (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists.solution
