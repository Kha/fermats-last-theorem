import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian
    {G : Scheme.{u}} [IsNoetherian G] (d : ℕ → ℕ)
    (ρ : ∀ (n : ℕ) {T : Scheme.{u}}, (T ⟶ G) → GL (Fin (d n)) Γ(T, ⊤))
    (hρ : ∀ (n : ℕ) {T T' : Scheme.{u}} (ψ : T' ⟶ T) (x : T ⟶ G),
      ρ n (ψ ≫ x) = Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ n x)) :
    ∃ N : ℕ, ∀ {T : Scheme.{u}} (x : T ⟶ G), (∀ n ≤ N, ρ n x = 1) → ∀ n, ρ n x = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian.solution
