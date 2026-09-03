import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_isLocalizedModule_of_span_range_eq_top

set_option autoImplicit false

universe u

theorem Module.Invertible.of_isLocalizedModule_of_span_range_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : Type u) [AddCommGroup N] [Module B N]
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (R : Fin k → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra B (R i)] [∀ i, IsLocalization.Away (f i) (R i)]
    [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower B (R i) (M i)]
    (π : ∀ i, N →ₗ[B] M i) (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (h : ∀ i, Module.Invertible (R i) (M i)) :
    Module.Invertible B N := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_isLocalizedModule_of_span_range_eq_top.solution
