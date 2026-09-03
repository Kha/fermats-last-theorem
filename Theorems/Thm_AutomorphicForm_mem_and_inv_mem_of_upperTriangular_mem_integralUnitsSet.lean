import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet

set_option autoImplicit false

theorem AutomorphicForm.mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
    {A : Type*} [CommRing A] (R : Set A) (hR : ∀ a ∈ R, ∀ b ∈ R, a * b ∈ R)
    (M : GL (Fin 2) A) (ζ a : Aˣ)
    (h10 : (M : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h11 : (M : Matrix (Fin 2) (Fin 2) A) 1 1 = ζ)
    (h00 : (M : Matrix (Fin 2) (Fin 2) A) 0 0 = a * ζ)
    (hM : M ∈ AutomorphicForm.integralUnitsSet R) :
    ((ζ : A) ∈ R ∧ ((ζ⁻¹ : Aˣ) : A) ∈ R) ∧ ((a : A) ∈ R ∧ ((a⁻¹ : Aˣ) : A) ∈ R) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet.solution
