import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import P2M.Util
import P2M.Sol.S_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map

set_option autoImplicit false
open CategoryTheory groupCohomology
open scoped Pointwise

theorem groupCohomology.Cores.map_subtype_cores_eq_finsum_cores_map
    {k G : Type} [CommRing k] [Group G] [Finite G] (A : Rep.{0} k G)
    (H D : Subgroup G) (τ : Cores.Transversal H)

    {ι : Type} [Finite ι] (g : ι → G)
    (hg : Function.Bijective fun i => DoubleCoset.mk D H (g i))
    (hone : ∃ i₀, g i₀ = 1)

    (τD : ∀ i, Cores.Transversal ((MulAut.conj (g i) • H).subgroupOf D))
    (c : ∀ i, ↥((MulAut.conj (g i) • H).subgroupOf D) →* ↥H)
    (hc : ∀ i (x : ↥((MulAut.conj (g i) • H).subgroupOf D)), ((c i x : ↥H) : G) = (g i)⁻¹ * ((x : ↥D) : G) * g i)
    (T : ∀ i, Rep.res (c i) (Rep.res H.subtype A) ⟶ Rep.res ((MulAut.conj (g i) • H).subgroupOf D).subtype (Rep.res D.subtype A))
    (hT : ∀ i (a : A), (T i).hom a = A.ρ (g i) a)
    (y : groupCohomology (Rep.res H.subtype A) 2) :
    (groupCohomology.map D.subtype (𝟙 (Rep.res D.subtype A)) 2).hom (Cores.cores A τ y) =
      ∑ᶠ i, Cores.cores (Rep.res D.subtype A) (τD i) ((groupCohomology.map (c i) (T i) 2).hom y) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map.solution
