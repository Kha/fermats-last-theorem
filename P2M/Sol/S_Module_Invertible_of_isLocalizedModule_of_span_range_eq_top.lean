import Mathlib
import Theorems.Thm_Module_Invertible_of_isLocalizedModule_of_span_eq_top
import P2M.Util
namespace P2MW.S_Module_Invertible_of_isLocalizedModule_of_span_range_eq_top

set_option autoImplicit false

universe u

theorem solution
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : Type u) [AddCommGroup N] [Module B N]
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (R : Fin k → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra B (R i)] [∀ i, IsLocalization.Away (f i) (R i)]
    [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower B (R i) (M i)]
    (π : ∀ i, N →ₗ[B] M i) (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (h : ∀ i, Module.Invertible (R i) (M i)) :
    Module.Invertible B N := by
  classical

  have hpre : ∀ g : ↥(Set.range f), ∃ i : Fin k, f i = g := fun g => g.2
  choose idx hidx using hpre

  haveI : ∀ g : ↥(Set.range f), IsLocalization.Away (g : B) (R (idx g)) := fun g => by
    rw [← hidx g]; infer_instance
  haveI : ∀ g : ↥(Set.range f), IsLocalizedModule (Submonoid.powers (g : B)) (π (idx g)) := fun g => by
    rw [← hidx g]; exact hπ (idx g)
  exact Module.Invertible.of_isLocalizedModule_of_span_eq_top (Set.range f) hf
    (Mₚ := fun g => M (idx g)) (Rₚ := fun g => R (idx g)) (fun g => π (idx g)) (fun g => h (idx g))
