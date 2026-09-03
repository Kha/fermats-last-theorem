import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one

set_option autoImplicit false

theorem AutomorphicForm.mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (t : Matrix.GeneralLinearGroup (Fin 2) L) :
    t ∈ AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ ↔
      (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) L) 0 0 ∈ Set.range (algebraMap F L) ∧
        (t : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap F L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one.solution
