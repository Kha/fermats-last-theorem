import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective
    {A₀ A : Type} [CommRing A₀] [CommRing A] [IsLocalRing A₀] [IsLocalRing A]
    (ι : A₀ →+* A) [IsLocalHom ι] (hres : Function.Surjective ((IsLocalRing.residue A).comp ι))
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    (iso : X ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (x : X) (hx : toBase.base x = closedPoint A) :
    let pr := iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    let c : A →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    let c₀ : A₀ →+* X₀.presheaf.stalk (pr.base x) :=
      (X₀.presheaf.germ ⊤ (pr.base x) trivial).hom.comp
        (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)

    (∀ a : A₀, (pr.stalkMap x).hom (c₀ a) = c (ι a)) ∧

    (∃ e : (X₀.presheaf.stalk (pr.base x) ⧸ (maximalIdeal A₀).map c₀) ≃+*
        (X.presheaf.stalk x ⧸ (maximalIdeal A).map c),
      ∀ s : X₀.presheaf.stalk (pr.base x),
        e (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ ((pr.stalkMap x).hom s)) ∧

    (∀ Q Q' : Ideal (X.presheaf.stalk x), Q'.IsPrime →
      (maximalIdeal A).map c ≤ Q → (maximalIdeal A).map c ≤ Q' →
      Q.comap (pr.stalkMap x).hom ≤ Q'.comap (pr.stalkMap x).hom → Q ≤ Q') ∧

    (∀ P : Ideal (X₀.presheaf.stalk (pr.base x)), P.IsPrime → (maximalIdeal A₀).map c₀ ≤ P →
      ∃ Q : Ideal (X.presheaf.stalk x), Q.IsPrime ∧ (maximalIdeal A).map c ≤ Q ∧
        Q.comap (pr.stalkMap x).hom = P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective.solution
