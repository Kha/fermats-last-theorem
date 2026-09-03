import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
namespace P2MW.S_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_left

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {A B N : Rep.{u} k G} (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (f : cocycles₁ A) (g : cocycles₁ B) (hf : (⇑f) ∈ coboundaries₁ A) (hg : IsLevelConstant₁ r (⇑g)) :
    (cup φ hφ f g : G × G → N) ∈ levelCoboundaries₂ r N := by
  obtain ⟨a, ha⟩ := hf
  have hfs : ∀ s : G, f s = A.ρ s a - a := fun s => by rw [← ha, d₀₁_hom_apply]
  refine (mem_levelCoboundaries₂_iff r N _).2 ⟨fun t => φ a (g t), hg.comp (fun b => φ a b), funext fun p => ?_⟩
  obtain ⟨s, t⟩ := p
  rw [d₁₂_hom_apply]
  show N.ρ s (φ a (g t)) - φ a (g (s * t)) + φ a (g s) = φ (f s) (B.ρ s (g t))
  rw [hfs s, (mem_cocycles₁_iff (⇑g)).1 g.2 s t, ← hφ s a (g t)]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  abel
