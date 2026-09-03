import Mathlib
import Definitions.Def_Deformations_TameDescent
import P2M.Util
import P2M.Sol.S_TaylorWiles_tameDescentChar_comp_eq

set_option autoImplicit false

universe u v w

open Function
theorem TaylorWiles.tameDescentChar_comp_eq {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g := by p2m_exact_reverting @_root_.P2MW.S_TaylorWiles_tameDescentChar_comp_eq.solution
