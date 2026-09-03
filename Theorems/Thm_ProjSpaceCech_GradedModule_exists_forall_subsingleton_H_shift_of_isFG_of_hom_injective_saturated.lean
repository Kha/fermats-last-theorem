import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D)
    (h : ProjSpaceCech.GradedModule.Hom D M) (hinj : Function.Injective h.toLinearMap)
    (hsat : ∀ (e : ℤ) (f : M.M), f ∈ M.grade e → ∀ j : Fin (n + 1),
      ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧ h.toLinearMap f' = (M.xMul j ^ N) f) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.solution
