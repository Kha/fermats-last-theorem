import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map
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
    (t : R) (htm : t ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤ Ideal.span {t} ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R))
    (ht : t ∉ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R)) :
    ∃ e : PowerSeries Λ ≃ₐ[Λ] R, e PowerSeries.X = t := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_forall_exists_comp_eq_of_notMem_sq_sup_map.solution
