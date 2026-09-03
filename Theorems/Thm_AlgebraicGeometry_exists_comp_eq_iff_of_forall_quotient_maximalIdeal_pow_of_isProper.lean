import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X Z₁ Z₂ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (ι₁ : Z₁ ⟶ X) (ι₂ : Z₂ ⟶ X) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (hfin : ((ι₂ ≫ f).base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite)
    (h : ∀ (k : ℕ) (R'' : Type u) [CommRing R''] (ψ : Spec (CommRingCat.of R'') ⟶ X),
      (∃ t : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))),
          t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))) = ψ ≫ f) →
        ((∃ ψ₁ : Spec (CommRingCat.of R'') ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R'') ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)))
    (R' : Type u) [CommRing R'] (ψ : Spec (CommRingCat.of R') ⟶ X) :
    (∃ ψ₁ : Spec (CommRingCat.of R') ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R') ⟶ Z₂, ψ₂ ≫ ι₂ = ψ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper.solution
