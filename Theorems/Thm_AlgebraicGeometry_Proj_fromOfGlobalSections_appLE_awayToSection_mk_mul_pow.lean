import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow

universe u v

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

theorem AlgebraicGeometry.Proj.fromOfGlobalSections_appLE_awayToSection_mk_mul_pow
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (g : A →+* Γ(X, ⊤)) (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    {n : ℕ} (hn : 0 < n) {r : A} (hr : r ∈ 𝒜 n) (k : ℕ) (s : A) (hs : s ∈ 𝒜 (k • n)) :
    (Proj.fromOfGlobalSections 𝒜 g hg).appLE (Proj.basicOpen 𝒜 r) (X.basicOpen (g r))
        (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 g hg hn hr).ge
        (Proj.awayToSection 𝒜 r (Away.mk 𝒜 hr k s hs)) *
      X.presheaf.map (homOfLE (X.basicOpen_le (g r))).op (g r) ^ k =
    X.presheaf.map (homOfLE (X.basicOpen_le (g r))).op (g s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow.solution
