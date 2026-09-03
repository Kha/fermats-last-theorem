import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range
attribute [-simp] BrauerNesbitt.actionEndoHom_apply BrauerNesbitt.actionTrace_apply BrauerNesbitt.actionEndo_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem Representation.exists_conj_eq_of_charpoly_eq_of_finite_range
    {G : Type*} [Group G] (ρ ρ' : G →* GL (Fin 2) ℂ)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ g : G, ρ' g = P * ρ g * P⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.solution
