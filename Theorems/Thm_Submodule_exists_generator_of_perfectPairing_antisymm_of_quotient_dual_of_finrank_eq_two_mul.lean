import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul

set_option autoImplicit false

theorem Submodule.exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {A : Type*} [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module 𝒪 P] [IsScalarTower 𝒪 A P]
    [Module.Finite 𝒪 P] [Module.Free 𝒪 P]
    (hrank : Module.finrank 𝒪 P = 2 * Module.finrank 𝒪 A)
    (β : P →ₗ[𝒪] P →ₗ[𝒪] 𝒪) (hβ : Function.Bijective β)
    (hanti : ∀ v w, β v w = - β w v) (hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w))
    (r : 𝒪) (hr : r ∈ IsLocalRing.maximalIdeal 𝒪) (hr0 : r ≠ 0)
    (E : Submodule A P) (hrE : ∀ w : P, r • w ∈ E)
    (Φ : P →ₗ[𝒪] (A →ₗ[𝒪] 𝒪 ⧸ Ideal.span {r})) (hΦs : Function.Surjective Φ)
    (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) (hΦa : ∀ (a : A) (v : P) (t : A), Φ (a • v) t = Φ v (a * t)) :
    ∃ x ∈ E, (∀ v ∈ E, ∃ (a : A) (w : P), v = a • x + r • w) ∧
      (∀ a : A, (∃ w : P, a • x = r • w) ↔ ∃ b : A, a = algebraMap 𝒪 A r * b) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul.solution
