import Mathlib
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.exists_sections_eq_of_forall_specMap_comp_eq
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)}
    {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)

    (A : ℕ → Type) [∀ n : ℕ, CommRing (A n)] (t : ∀ n : ℕ, A (n + 1) →+* A n)
    (κ : ∀ n : ℕ, Spec (CommRingCat.of (A n)) ⟶ X n) (hκ : ∀ n : ℕ, IsOpenImmersion (κ n))
    (hκt : ∀ n : ℕ, κ n ≫ xt n = Spec.map (CommRingCat.ofHom (t n)) ≫ κ (n + 1))

    (U : ∀ n : ℕ, (D.Y n).Opens)
    (hU : ∀ n : ℕ, (U n : Set (D.Y n)) = Set.range (κ n ≫ D.p n).base)
    (hUt : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (U (n + 1)) = U n)

    (fam : ∀ n : ℕ, A n) (hfam : ∀ n : ℕ, t n (fam (n + 1)) = fam n)
    (hagree : ∀ (n : ℕ) (g : G) (B : Type) [CommRing B] (x x' : A n →+* B),
      Spec.map (CommRingCat.ofHom x) ≫ κ n = (Spec.map (CommRingCat.ofHom x') ≫ κ n) ≫ (a n g).hom → x (fam n) = x' (fam n)) :
    ∃ s : ∀ n : ℕ, ↑((D.Y n).presheaf.obj (Opposite.op (U n))),
      (∀ (n : ℕ) (hle : U n ≤ (D.yt n) ⁻¹ᵁ (U (n + 1))),
        (D.Y n).presheaf.map (homOfLE hle).op (((D.yt n).app (U (n + 1))).hom (s (n + 1))) = s n) ∧
      ∀ (n : ℕ) (hle : (⊤ : (Spec (CommRingCat.of (A n))).Opens) ≤ (κ n ≫ D.p n) ⁻¹ᵁ (U n)),
        (Scheme.ΓSpecIso (CommRingCat.of (A n))).hom.hom
          ((Spec (CommRingCat.of (A n))).presheaf.map (homOfLE hle).op (((κ n ≫ D.p n).app (U n)).hom (s n))) = fam n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq.solution
