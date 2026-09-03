import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
open scoped Pointwise
theorem Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (ρ : R →+* Module.End ℤ J) (hρ : ∀ (t : R) (x : J), t • x = ρ t x)
    (S : Subalgebra ℤ (Module.End ℤ J)) (hS : (Subalgebra.toSubmodule S).FG)
    (hρS : ∀ t, ρ t ∈ S)
    (I γ : Ideal R) (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → t ∈ γ)
    (z : J ⧸ (γ • (⊤ : Submodule R J)))
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z := by p2m_exact_reverting @_root_.P2MW.S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg.solution
