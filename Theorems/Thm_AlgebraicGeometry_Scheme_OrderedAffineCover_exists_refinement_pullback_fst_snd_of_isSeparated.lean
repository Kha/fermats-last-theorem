import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_pullback_fst_snd_of_isSeparated
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : A.OrderedAffineCover) (μ : pullback f f ⟶ A) (hμ : μ ≫ f = pullback.fst f f ≫ f) :
    ∃ (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧
      (∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w)) ∧
      (∀ w, 𝒲.U w ≤ μ ⁻¹ᵁ 𝒦.U (lam₃ w)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated.solution
