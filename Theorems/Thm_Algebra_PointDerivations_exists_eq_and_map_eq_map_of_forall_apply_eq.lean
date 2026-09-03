import Mathlib
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_Algebra_PointDerivations_exists_eq_and_map_eq_map_of_forall_apply_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.PointDerivations.exists_eq_and_map_eq_map_of_forall_apply_eq
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)
    (M M' N : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] [AddCommGroup N] [Module k N]
    (c : ↥(Algebra.PointDerivations k A ev M)) (g : M →ₗ[k] N) (σ : M' →ₗ[k] N) (hσ : Function.Injective σ)
    (cs : A → M') (h : ∀ a : A, σ (cs a) = g (c.1 a)) :
    ∃ δ : ↥(Algebra.PointDerivations k A ev M'),
      (∀ a : A, δ.1 a = cs a) ∧ Algebra.PointDerivations.map ev σ δ = Algebra.PointDerivations.map ev g c := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PointDerivations_exists_eq_and_map_eq_map_of_forall_apply_eq.solution
