import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {E : Scheme.{u}} (ι : E ⟶ J)
    {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
    [Flat p] [Surjective p]
    (hcoeq : IsColimit (Cofork.ofπ p w))
    {g : P ⟶ Spec (CommRingCat.of R)} (hg : p ≫ g = f) (LP : RelativeGroupLaw R g)
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
        LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩)
    {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} (LX : RelativeGroupLaw R gX)
    (φ : SchemeHomOver f gX)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(L.mul t x y).1 ≫ φ.1, by rw [Category.assoc, φ.2, (L.mul t x y).2]⟩ : SchemeHomOver t gX) =
        LX.mul t ⟨x.1 ≫ φ.1, by rw [Category.assoc, φ.2, x.2]⟩ ⟨y.1 ≫ φ.1, by rw [Category.assoc, φ.2, y.2]⟩)
    (hφE : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (he : e ≫ ι ≫ f = t),
      (⟨(e ≫ ι) ≫ φ.1, by simp only [Category.assoc, φ.2, he]⟩ : SchemeHomOver t gX) = LX.one t) :
    ∃! ψ : SchemeHomOver g gX, p ≫ ψ.1 = φ.1 ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t gX) =
          LX.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit.solution
