import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber

set_option autoImplicit false

universe u v

p2m_open "IsLocalRing~exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map"

theorem IsLocalRing.exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra Λ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (hsmooth : ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        [IsArtinianRing A] [IsArtinianRing B] [Algebra Λ A] [Algebra Λ B],
        Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap Λ A)) →
        Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap Λ B)) →
        ∀ π : B →ₐ[Λ] A, Function.Surjective π →
        (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
        ∀ g : R →ₐ[Λ] A, ∃ g' : R →ₐ[Λ] B, π.comp g' = g)
    (Φ₁ : R →ₐ[Λ] DualNumber (ResidueField R)) (hΦ₁ : ∀ r : R, (Φ₁ r).fst = residue R r)
    (hΦ₁' : ∃ r : R, (Φ₁ r).snd ≠ 0)
    (hdim : ∀ Φ : R →ₐ[Λ] DualNumber (ResidueField R), (∀ r : R, (Φ r).fst = residue R r) →
      ∃ c : ResidueField R, ∀ r : R, (Φ r).snd = c * (Φ₁ r).snd) :
    ∃ e : PowerSeries Λ ≃ₐ[Λ] R, (Φ₁ (e PowerSeries.X)).snd ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber.solution
