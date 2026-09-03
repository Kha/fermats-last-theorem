import Mathlib
import P2M.Util
import P2M.Sol.S_FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero

set_option autoImplicit false

open Submodule

theorem FixedPart.exists_smul_eq_zero_forall_of_comp_eq_zero
    (T : Type) [CommRing T] [IsReduced T] [IsArtinianRing T]
    (V : Type) [AddCommGroup V] [Module T V] (e : V ≃ₗ[T] (Fin 2 → T))
    {ι : Type} (g : ι → V →ₗ[T] V) (hgg : ∀ i j : ι, g i ∘ₗ g j = 0) :
    ∃ v : V, (∀ i : ι, g i v = 0) ∧ ∀ t : T, t • v = 0 → t = 0 := by p2m_exact_reverting @_root_.P2MW.S_FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero.solution
