import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one

set_option autoImplicit false

theorem AutomorphicForm.bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (t' : GL (Fin 2) L)
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (M : Subgroup (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {κ : Type*} (a : κ → GL (Fin 2) L)
    (haD : ∀ j, ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M) :
    Set.BijOn (fun p : κ × Lˣ × L =>
        a p.1 * t' * Matrix.GeneralLinearGroup.map (σ : L →+* L) (AutomorphicForm.unipotentGL2 p.2.2) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) p.2.1 * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (a p.1))⁻¹)
      Set.univ J := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one.solution
