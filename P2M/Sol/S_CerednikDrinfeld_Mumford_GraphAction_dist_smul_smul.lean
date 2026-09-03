import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul

set_option autoImplicit false

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.GraphAction"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "GraphAction GraphAction.smul_adj"
namespace Isom
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

def smulHom (g : G) : 𝒯 →g 𝒯 where
  toFun := fun w => g • w
  map_rel' := fun h => GraphAction.smul_adj g h

theorem dist_smul_le (g : G) (x y : W) : 𝒯.dist (g • x) (g • y) ≤ 𝒯.dist x y := by
  by_cases h : 𝒯.Reachable x y
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    have := SimpleGraph.dist_le (p.map (smulHom 𝒯 g))
    rw [SimpleGraph.Walk.length_map, hp] at this
    exact this
  ·
    have h' : ¬ 𝒯.Reachable (g • x) (g • y) := by
      intro hr
      apply h
      obtain ⟨p⟩ := hr
      have q : 𝒯.Walk (g⁻¹ • (g • x)) (g⁻¹ • (g • y)) := p.map (smulHom 𝒯 g⁻¹)
      rw [inv_smul_smul, inv_smul_smul] at q
      exact ⟨q⟩
    rw [SimpleGraph.dist_eq_zero_of_not_reachable h, SimpleGraph.dist_eq_zero_of_not_reachable h']

theorem main (g : G) (x y : W) : 𝒯.dist (g • x) (g • y) = 𝒯.dist x y := by
  refine le_antisymm (dist_smul_le 𝒯 g x y) ?_
  have := dist_smul_le 𝒯 g⁻¹ (g • x) (g • y)
  rwa [inv_smul_smul, inv_smul_smul] at this

end CerednikDrinfeld.Mumford.Isom

theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (g : G) (x y : W) :
    𝒯.dist (g • x) (g • y) = 𝒯.dist x y :=
  CerednikDrinfeld.Mumford.Isom.main 𝒯 g x y
