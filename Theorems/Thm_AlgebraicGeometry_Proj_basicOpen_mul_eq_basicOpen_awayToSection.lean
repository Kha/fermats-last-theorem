import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f g : A} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') :
    Proj.basicOpen 𝒜 (f * g) =
      (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection.solution
