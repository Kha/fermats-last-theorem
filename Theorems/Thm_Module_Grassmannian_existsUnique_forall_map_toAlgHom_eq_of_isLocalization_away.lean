import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A) (hf : Ideal.span (Set.range f) = ⊤)
    (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
    [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
    (N : ∀ i, Module.Grassmannian (B i) (B i ⊗[R] M) k)
    (hN : ∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
        [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
        Module.Grassmannian.map (ρ₁.restrictScalars R) (N i) =
          Module.Grassmannian.map (ρ₂.restrictScalars R) (N j)) :
    ∃! N₀ : Module.Grassmannian A (A ⊗[R] M) k,
      ∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (B i)) N₀ = N i := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away.solution
