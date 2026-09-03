import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.TowerQuotientDatum.existsUnique_forall_p_comp_eq
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (T : Scheme.{0}) (w : ∀ n : ℕ, X n ⟶ T)
    (hinv : ∀ (n : ℕ) (g : G), (a n g).hom ≫ w n = w n)
    (hxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n) :
    ∃! u : ∀ n : ℕ, D.Y n ⟶ T, ∀ n : ℕ, D.p n ≫ u n = w n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq.solution
