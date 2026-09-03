import Mathlib
import P2M.Util
import P2M.Sol.S_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ

set_option autoImplicit false

universe u v w x y

theorem AddTorsor.bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ
    {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V] {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (τ : V →ₗ[k] W)
    {LA : Type x} [AddTorsor V LA] {LG : Type y} [AddAction W LG] [AddAction.IsPretransitive W LG]
    (f : LA → LG) (hf : ∀ (v : V) (a : LA), f (v +ᵥ a) = τ v +ᵥ f a) (hinj : Function.Injective f)
    (U : Submodule k V) [FiniteDimensional k ↥U] (hdim : Module.finrank k W ≤ Module.finrank k ↥U) :
    Function.Bijective τ ∧ Function.Surjective f := by p2m_exact_reverting @_root_.P2MW.S_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ.solution
