import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TowerQuotientDatum_p_base_eq_iff_and_preimage_image_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.p_base_eq_iff_and_preimage_image_eq
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)}
    {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a) (n : ℕ) :
    (∀ x x' : X n, (D.p n).base x = (D.p n).base x' ↔ ∃ g : G, (a n g).hom.base x = x') ∧
    ∀ W : Set (X n), (D.p n).base ⁻¹' ((D.p n).base '' W) = ⋃ g : G, (a n g).hom.base '' W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TowerQuotientDatum_p_base_eq_iff_and_preimage_image_eq.solution
