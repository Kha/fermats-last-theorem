import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.exists_preimage_eq_of_isPullback_of_forall_preimage_eq
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (X' Y' : ℕ → Scheme.{0}) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (p' : ∀ n : ℕ, X' n ⟶ Y' n) (q : ∀ n : ℕ, X' n ⟶ X n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (n : ℕ) :
    Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
    (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
    (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq.solution
