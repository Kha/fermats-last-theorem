import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
namespace P2MW.S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (N : Subgroup G) [N.Normal] (x : H1 M) :
    x ∈ inflationImage M N ↔ ∃ c : cocycles₁ M, H1π M c = x ∧ ∀ n ∈ N, c n = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using H1_induction_on with | h z =>
    refine ⟨mapCocycles₁ (QuotientGroup.mk' N) (Rep.ofHom (M.ρ.quotientToInvariants_lift N)) z,
      ?_, ?_⟩
    · exact (show (inflation M N).hom (H1π (M.quotientToInvariants N) z)
          = H1π M (mapCocycles₁ (QuotientGroup.mk' N)
              (Rep.ofHom (M.ρ.quotientToInvariants_lift N)) z) from
        H1π_comp_map_apply _ _ _).symm
    intro n hn
    have h1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show (z ((QuotientGroup.mk' N) n)).1 = 0
    rw [h1, cocycles₁_map_one]
    rfl
  · rintro ⟨c, rfl, hc⟩
    have hexact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (H1InfRes_exact M N)
    change H1π M c ∈ LinearMap.range (ModuleCat.Hom.hom (H1InfRes M N).f)
    rw [hexact]
    have hres : ModuleCat.Hom.hom (H1InfRes M N).g (H1π M c)
        = H1π (Rep.res N.subtype M) (mapCocycles₁ N.subtype (𝟙 _) c) :=
      H1π_comp_map_apply _ _ _
    have hzero : mapCocycles₁ N.subtype (𝟙 (Rep.res N.subtype M)) c = 0 :=
      cocycles₁_ext fun n => hc n.1 n.2
    change (ModuleCat.Hom.hom (H1InfRes M N).g) (H1π M c) = 0
    refine hres.trans ?_
    rw [hzero]
    exact map_zero _
