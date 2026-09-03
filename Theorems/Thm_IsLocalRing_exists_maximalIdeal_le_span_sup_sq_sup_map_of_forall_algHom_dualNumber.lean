import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_maximalIdeal_le_span_sup_sq_sup_map_of_forall_algHom_dualNumber

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_maximalIdeal_le_span_sup_sq_sup_map_of_forall_algHom_dualNumber
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra Λ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (Φ₁ : R →ₐ[Λ] DualNumber (ResidueField R)) (hΦ₁ : ∀ r : R, (Φ₁ r).fst = residue R r)
    (hdim : ∀ Φ : R →ₐ[Λ] DualNumber (ResidueField R), (∀ r : R, (Φ r).fst = residue R r) →
      ∃ c : ResidueField R, ∀ r : R, (Φ r).snd = c * (Φ₁ r).snd) :
    ∃ t ∈ maximalIdeal R,
      maximalIdeal R ≤ Ideal.span {t} ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal Λ).map (algebraMap Λ R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_maximalIdeal_le_span_sup_sq_sup_map_of_forall_algHom_dualNumber.solution
