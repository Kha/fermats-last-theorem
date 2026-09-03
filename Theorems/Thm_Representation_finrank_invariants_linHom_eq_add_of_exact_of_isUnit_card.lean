import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card

set_option autoImplicit false
universe u
open Module
theorem Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {VN VA VB VC : Type*} [AddCommGroup VN] [Module k VN] [AddCommGroup VA] [Module k VA]
    [AddCommGroup VB] [Module k VB] [AddCommGroup VC] [Module k VC]
    [FiniteDimensional k VN] [FiniteDimensional k VB]
    (N : Representation k Δ VN) (A : Representation k Δ VA) (B : Representation k Δ VB) (C : Representation k Δ VC)
    (f : VA →ₗ[k] VB) (g : VB →ₗ[k] VC) (hf : ∀ d, f ∘ₗ A d = B d ∘ₗ f) (hg : ∀ d, g ∘ₗ B d = C d ∘ₗ g)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    finrank k (N.linHom B).invariants = finrank k (N.linHom A).invariants + finrank k (N.linHom C).invariants := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card.solution
