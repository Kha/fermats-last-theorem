import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R S))) (ϖ : R) (q : ↥(Spec (CommRingCat.of S))) :
    ¬ ((Ideal.span {(X.presheaf.germ ⊤ (ι.base q) trivial).hom
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))} : Ideal (X.presheaf.stalk (ι.base q))).minimalPrimes).Subsingleton ↔
    ∃ 𝔭 ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes, ∃ 𝔭' ∈ (Ideal.span {algebraMap R S ϖ}).minimalPrimes,
      𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q.asIdeal ∧ 𝔭' ≤ q.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart.solution
