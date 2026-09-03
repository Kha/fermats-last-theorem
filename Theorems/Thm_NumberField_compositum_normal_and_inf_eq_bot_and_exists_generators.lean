import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_compositum_normal_and_inf_eq_bot_and_exists_generators

set_option autoImplicit false

theorem NumberField.compositum_normal_and_inf_eq_bot_and_exists_generators
    (E F L N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra E F] [Algebra E L] [Algebra E N] [Algebra F N] [Algebra L N]
    [IsScalarTower E F N] [IsScalarTower E L N] [IsGalois E F] [IsGalois E L] [IsGalois E N]
    (hL : IsCyclic (L ≃ₐ[E] L))
    (hdeg : Module.finrank E L = Module.finrank E F)
    (hgen : ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) →
      (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1) :
    ∃ (_ : ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup.Normal)
      (_ : ((IsScalarTower.toAlgHom E L N).fieldRange).fixingSubgroup.Normal),
      ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup ⊓
          ((IsScalarTower.toAlgHom E L N).fieldRange).fixingSubgroup = ⊥ ∧
      Nat.card ((N ≃ₐ[E] N) ⧸ ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup)
          = Nat.card (F ≃ₐ[E] F) ∧
      (∃ s : (N ≃ₐ[E] N) ⧸ ((IsScalarTower.toAlgHom E L N).fieldRange).fixingSubgroup,
        (∀ g, g ∈ Subgroup.zpowers s) ∧
        orderOf s = Nat.card ((N ≃ₐ[E] N) ⧸ ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup)) ∧
      (∃ t : ↥((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup,
        ∀ g, g ∈ Subgroup.zpowers t) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_compositum_normal_and_inf_eq_bot_and_exists_generators.solution
