import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne NeronModelInfra GoodReductionJacobian"

theorem GoodReductionJacobian.RelativeGroupLaw.exists_spec_glued_charts
    {R A' : Type u} [CommRing R] [IsLocalRing R] [CommRing A'] [IsLocalRing A']
    (φA : R →+* A') [IsLocalHom φA]
    {G N : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {gN : N ⟶ Spec (CommRingCat.of R)} (LN : RelativeGroupLaw R gN)
    {Φ : Type u} [AddCommGroup Φ]
    (e : Φ → (G ⟶ N)) (he : ∀ φ, IsOpenImmersion (e φ)) (hef : ∀ φ, e φ ≫ gN = f)
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (hne : ∀ φ ψ, φ ≠ ψ → ∀ n ∈ Set.range (e φ).base ∩ Set.range (e ψ).base,
      gN.base n ≠ IsLocalRing.closedPoint R)
    (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hchart : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f),
        LN.mul s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩)
            (NeronModelInfra.schemeHomOverComp b ⟨e ψ, hef ψ⟩) =
          NeronModelInfra.schemeHomOverComp
            (L.mul s (L.mul s a b) (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c φ ψ)))
            ⟨e (φ + ψ), hef (φ + ψ)⟩) :
    ∃ spec : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN → Φ,
      (∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN) (φ : Φ),
        spec s = φ ↔ ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) f,
          NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩ = s) ∧
      (∀ s s' : SchemeHomOver (Spec.map (CommRingCat.ofHom φA)) gN,
        spec (LN.mul _ s s') = spec s + spec s') ∧
      Function.Surjective spec := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_spec_glued_charts.solution
