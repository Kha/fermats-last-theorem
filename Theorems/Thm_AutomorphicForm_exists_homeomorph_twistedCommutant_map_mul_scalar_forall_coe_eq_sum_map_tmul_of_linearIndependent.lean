import Definitions.Def_AutomorphicForm_TwistedCommutant
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ)
    (ι : Type) [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hspan : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ↔
        x ∈ Submodule.span K (Set.range b)) :
    ∃ e : (ι → A) ≃ₜ ↥(AutomorphicForm.twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ∀ a : ι → A,
        ((e a : AutomorphicForm.twistedCommutant K L A σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        ∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent.solution
