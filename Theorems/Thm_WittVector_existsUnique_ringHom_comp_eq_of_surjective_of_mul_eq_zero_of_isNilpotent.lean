import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent

set_option autoImplicit false

universe u

open WittVector

theorem WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B B₀ : Type u) [CommRing B] [CommRing B₀] (q : B →+* B₀) (hq : Function.Surjective q)
    (hsq : ∀ s t : B, q s = 0 → q t = 0 → s * t = 0) (hpB : IsNilpotent (p : B))
    (ψ₀ : WittVector p k →+* B₀) :
    ∃! ψ : WittVector p k →+* B, q.comp ψ = ψ₀ := by p2m_exact_reverting @_root_.P2MW.S_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent.solution
