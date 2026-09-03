import Mathlib
import P2M.Util
import P2M.Sol.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem IsGalois.exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
    (E C : Type) [Field E] [Field C] [Algebra E C] [FiniteDimensional E C] [IsGalois E C]
    (p k : ℕ) [Fact p.Prime] (χ : (C ≃ₐ[E] C) →* (ZMod (p ^ k))ˣ) (hχ : Function.Injective χ) :
    ∃ (M : Subgroup (C ≃ₐ[E] C)) (_ : M.Normal),
      (∀ g : C ≃ₐ[E] C, χ g = -1 → g ∈ M) ∧
      Nat.card M ≤ 2 * (p - 1) ∧
      IsGalois E (IntermediateField.fixedField M) ∧
      IsCyclic ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) ∧
      IsPGroup p ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) ∧
      Nat.card ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) * Nat.card M = Nat.card (C ≃ₐ[E] C) := by p2m_exact_reverting @_root_.P2MW.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units.solution
