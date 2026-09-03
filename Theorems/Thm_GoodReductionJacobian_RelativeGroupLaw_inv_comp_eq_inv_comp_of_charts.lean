import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.inv_comp_eq_inv_comp_of_charts
    {S B₁ B₂ : Type u} [CommRing S] [CommRing B₁] [CommRing B₂] [Algebra S B₁] [Algebra S B₂]
    {Y A₁ A₂ : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (ι₁ : A₁ ⟶ Y)
    (h₁ : ι₁ ≫ f = f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)))
    (f₂ : A₂ ⟶ Spec (CommRingCat.of B₂)) (ι₂ : A₂ ⟶ Y) [Mono ι₂]
    (h₂ : IsPullback ι₂ f₂ f (Spec.map (CommRingCat.ofHom (algebraMap S B₂))))
    (L₁ : RelativeGroupLaw B₁ f₁) (L₂ : RelativeGroupLaw B₂ f₂)
    (hagree : ∀ {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of B₁)) (t₂ : T ⟶ Spec (CommRingCat.of B₂))
        (a b : SchemeHomOver t₁ f₁) (a' b' : SchemeHomOver t₂ f₂),
        a.1 ≫ ι₁ = a'.1 ≫ ι₂ → b.1 ≫ ι₁ = b'.1 ≫ ι₂ → (L₁.mul t₁ a b).1 ≫ ι₁ = (L₂.mul t₂ a' b').1 ≫ ι₂)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of B₁)) (t₂ : T ⟶ Spec (CommRingCat.of B₂))
    (ht : t₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)) = t₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₂)))
    (x : SchemeHomOver t₁ f₁) (x' : SchemeHomOver t₂ f₂) (hx : x.1 ≫ ι₁ = x'.1 ≫ ι₂) :
    (L₁.inv t₁ x).1 ≫ ι₁ = (L₂.inv t₂ x').1 ≫ ι₂ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts.solution
