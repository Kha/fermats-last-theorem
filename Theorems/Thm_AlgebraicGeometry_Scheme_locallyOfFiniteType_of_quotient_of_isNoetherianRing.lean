import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.locallyOfFiniteType_of_quotient_of_isNoetherianRing
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪)) (hlft : LocallyOfFiniteType fM)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = U) :
    LocallyOfFiniteType f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing.solution
