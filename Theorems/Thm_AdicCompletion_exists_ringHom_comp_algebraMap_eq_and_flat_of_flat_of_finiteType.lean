import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType

set_option autoImplicit false

universe u

theorem AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
    {B₀ : Type u} [CommRing B₀] [IsNoetherianRing B₀] {B : Type u} [CommRing B] [Algebra B₀ B]
    [Module.Flat B₀ B] [Algebra.FiniteType B₀ B] (I₀ : Ideal B₀) :
    ∃ f : AdicCompletion I₀ B₀ →+* AdicCompletion (I₀.map (algebraMap B₀ B)) B,
      (∀ b : B₀, f (algebraMap B₀ (AdicCompletion I₀ B₀) b)
        = algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (algebraMap B₀ B b)) ∧
      (letI := f.toAlgebra; Module.Flat (AdicCompletion I₀ B₀) (AdicCompletion (I₀.map (algebraMap B₀ B)) B)) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType.solution
