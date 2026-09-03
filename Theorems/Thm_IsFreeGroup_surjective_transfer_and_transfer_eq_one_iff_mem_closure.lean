import Mathlib
import P2M.Util
import P2M.Sol.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure

set_option autoImplicit false

theorem IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure
    {F : Type*} [Group F] [IsFreeGroup F] (R : Subgroup F) [R.Normal] [R.FiniteIndex]
    (hR : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ R) (A : Type*) [CommGroup A] :
    Function.Surjective (fun χ : ↥R →* A => MonoidHom.transfer χ) ∧
    ∀ χ : ↥R →* A, MonoidHom.transfer χ = 1 ↔
      χ ∈ Subgroup.closure {ψ : ↥R →* A | ∃ (g : F) (χ' : ↥R →* A),
        ψ = (χ'.comp (MulAut.conjNormal g : MulAut ↥R).toMonoidHom) / χ'} := by p2m_exact_reverting @_root_.P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure.solution
