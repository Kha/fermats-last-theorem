import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

theorem AlgebraicGeometry.Scheme.exists_crossingChart_of_crossingPresentation_stalk
    {O : Type u} [CommRing O] [IsNoetherianRing O] (ϖ : O) (e : ℕ)
    [IsDomain (CrossingQuotient O (ϖ ^ e))] [IsIntegrallyClosed (CrossingQuotient O (ϖ ^ e))]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (πX : X ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType πX]
    (x : X) (hx : IsClosed ({x} : Set X))

    (g h : X.presheaf.stalk x)
    (hrel : g * h = (X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ))) ^ e)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)), g, h})

    (hres : Function.Surjective fun o : O => IsLocalRing.residue (X.presheaf.stalk x)
      (X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))))

    (hdim : ringKrullDim (CrossingQuotient O (ϖ ^ e)) ≤ ringKrullDim (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (gU hU : Γ(X, U))
      (f : (U : Scheme.{u}) ⟶ CrossingQuotient.crossingScheme (ϖ ^ e)),
      X.presheaf.germ U x hxU gU = g ∧ X.presheaf.germ U x hxU hU = h ∧
      gU * hU = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ))) ^ e ∧

      f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e)))) = U.ι ≫ πX ∧

      (∀ y : ↥(U : Scheme.{u}),
          (CrossingQuotient.U (ϖ ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (ϖ ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = x) ∧

      (∀ y : ↥(U : Scheme.{u}), U.ι.base y = x →
          (f.stalkMap y).hom.Flat ∧
          Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
          IsIso (f.residueFieldMap y)) ∧

      (∀ y : ↥(U : Scheme.{u}), CrossingQuotient.U (ϖ ^ e) ∈ (f.base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen gU) ∧
      (∀ y : ↥(U : Scheme.{u}), CrossingQuotient.V (ϖ ^ e) ∈ (f.base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen hU) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk.solution
