import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_exact_tateMap_tateDelta
import Theorems.Thm_Rep_exact_tateDelta_tateMap
import P2M.Util
namespace P2MW.S_Rep_bijective_tateDelta_of_isZero

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology n))
    (h₁ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology (n + 1))) :
    Function.Bijective (Rep.tateδ hX n).hom := by
  have zelt : ∀ {M : ModuleCat.{u} k}, CategoryTheory.Limits.IsZero M → ∀ x : M, x = 0 := fun hM x => by
    simpa using congrArg (fun ψ => ψ.hom x) (hM.eq_of_src (𝟙 _) 0)
  constructor
  · have ex := Rep.exact_tateMap_tateDelta hX n
    intro y₁ y₂ h
    have h0 : (Rep.tateδ hX n).hom (y₁ - y₂) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨x, hx⟩ := (ex (y₁ - y₂)).1 h0
    rw [zelt h₀ x] at hx
    exact sub_eq_zero.1 (hx.symm.trans (map_zero _))
  · have ex := Rep.exact_tateDelta_tateMap hX n
    intro y
    obtain ⟨x, hx⟩ := (ex y).1 (zelt h₁ _)
    exact ⟨x, hx⟩
