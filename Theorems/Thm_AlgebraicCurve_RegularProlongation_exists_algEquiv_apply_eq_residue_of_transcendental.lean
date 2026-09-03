import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental

set_option autoImplicit false

open AlgebraicCurve Polynomial

universe u v w w'

theorem AlgebraicCurve.RegularProlongation.exists_algEquiv_apply_eq_residue_of_transcendental
    {L : Type u} [Field L] (V : ValuationSubring L)
    {F' : Type v} [Field F'] [Algebra L F']
    {Fb : Type w} [Field Fb] [Algebra (IsLocalRing.ResidueField V) Fb]
    (R : RegularProlongation V F' Fb)
    (y : F') (hy : y ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F']
    (htr : Transcendental (IsLocalRing.ResidueField V) (R.residue ⟨y, hy⟩))
    {F : Type w'} [Field F] [Algebra (IsLocalRing.ResidueField V) F]
    (Λ : Subring F') (hΛ : ∀ f : F', f ∈ Λ → f ∈ R.integers)
    (hyΛ : y ∈ Λ) (hVΛ : ∀ a : V, algebraMap L F' a ∈ Λ)
    (hint : ∀ f : Λ, ∃ P : (Polynomial V)[X], P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y)
        (f : F') P = 0)
    (ρ : Λ →+* F)
    (hρV : ∀ a : V, ρ ⟨algebraMap L F' a, hVΛ a⟩ =
      algebraMap (IsLocalRing.ResidueField V) F (IsLocalRing.residue V a))
    (hker : ∀ f : Λ, ρ f = 0 → R.residue ⟨f, hΛ f f.2⟩ = 0)
    (hfrac : ∀ z : F, ∃ f h : Λ, ρ h ≠ 0 ∧ z * ρ h = ρ f)
    [FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField V) ({ρ ⟨y, hyΛ⟩} : Set F)) F]
    (hdeg : Module.finrank (IntermediateField.adjoin L ({y} : Set F')) F' ≤
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) ({ρ ⟨y, hyΛ⟩} : Set F)) F) :
    ∃ θ : F ≃ₐ[IsLocalRing.ResidueField V] Fb, ∀ f : Λ, θ (ρ f) = R.residue ⟨f, hΛ f f.2⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental.solution
