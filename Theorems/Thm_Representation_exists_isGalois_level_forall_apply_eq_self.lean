import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_isGalois_level_forall_apply_eq_self

set_option autoImplicit false
theorem Representation.exists_isGalois_level_forall_apply_eq_self
    {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [Module.Finite k V]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ρ : Representation k G V)
    (hsm : ∀ m : V, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → ρ s m = m) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → ∀ m : V, ρ s m = m := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_isGalois_level_forall_apply_eq_self.solution
