import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (x : X) (hx : x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base)
    (hc0 : ∀ h0 : x ∈ 𝒱.U0, ((X.presheaf.germ 𝒱.U0 x h0).hom : (𝒱.cover c).A0 →+* X.presheaf.stalk x).comp
        (algebraMap R (𝒱.cover c).A0) =
      ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).comp
        (RingHom.id R))
    (hc1 : ∀ h1 : x ∈ 𝒱.U1, ((X.presheaf.germ 𝒱.U1 x h1).hom : (𝒱.cover c).A1 →+* X.presheaf.stalk x).comp
        (algebraMap R (𝒱.cover c).A1) =
      ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).comp
        (RingHom.id R)) :
    letI : Algebra R (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    (∀ (h0 : x ∈ 𝒱.U0) (ω₀ : Ω[(𝒱.cover c).A0⁄R]) (η : Ω[X.presheaf.stalk x⁄R]),
        KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A0) (B := X.presheaf.stalk x)
          (RingHom.id R) (X.presheaf.germ 𝒱.U0 x h0).hom (hc0 h0) ω₀ = ϖ • η →
        ∃ α : Ω[(𝒱.cover c).A0⁄R], ω₀ = ϖ • α) ∧
    (∀ (h1 : x ∈ 𝒱.U1) (ω₁ : Ω[(𝒱.cover c).A1⁄R]) (η : Ω[X.presheaf.stalk x⁄R]),
        KaehlerDifferential.mapOfRingHom (A := (𝒱.cover c).A1) (B := X.presheaf.stalk x)
          (RingHom.id R) (X.presheaf.germ 𝒱.U1 x h1).hom (hc1 h1) ω₁ = ϖ • η →
        ∃ α : Ω[(𝒱.cover c).A1⁄R], ω₁ = ϖ • α) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_smul_chart_of_mapOfRingHom_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.solution
