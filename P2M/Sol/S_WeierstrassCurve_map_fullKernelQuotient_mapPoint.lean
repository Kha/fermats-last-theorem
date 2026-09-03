import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_MapPoint
import P2M.Util
namespace P2MW.S_WeierstrassCurve_map_fullKernelQuotient_mapPoint

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₁ map map_b₂ a₆ toAffine map_a₆ map_a₁ map_a₄ map_a₂ map_a₃ fullKernelQuotient oddOrderSummingSet veluQuotientOfSums veluGx veluGy mapPoint mapPoint_nsmul"
namespace FullKernelQuotientBaseChange
p2m_open "WeierstrassCurve"

variable {F K : Type*} [Field F] [Field K] (f : F →+* K)

private theorem coordsOrZero_mapPoint {W : WeierstrassCurve F} (P : W.toAffine.Point) :
    (mapPoint f P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0 : K), (0 : K)) = (f 0, f 0)
    rw [map_zero]
  · rfl

private theorem oddOrderSummingSet_mapPoint [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (mapPoint f Q) n = (W.oddOrderSummingSet Q n).image (Prod.map f f) := by
  rw [oddOrderSummingSet, oddOrderSummingSet, Finset.image_image]
  congr 1
  funext k
  simp only [Function.comp_apply, ← mapPoint_nsmul, coordsOrZero_mapPoint]

private theorem sum_image_prodMap [DecidableEq K] (S : Finset (F × F)) (g : K × K → K) :
    ∑ P ∈ S.image (Prod.map f f), g P = ∑ P ∈ S, g (Prod.map f f P) :=
  Finset.sum_image fun _ _ _ _ h => (f.injective.prodMap f.injective) h

private theorem veluGx_map (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, map_a₁, map_a₂, map_a₄, map_sub, map_add, map_mul, map_pow, map_ofNat]

private theorem veluGy_map (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [veluGy, map_a₁, map_a₃, map_neg, map_add, map_mul, map_ofNat]

private theorem veluQuotientOfSums_map (W : WeierstrassCurve F) (t w : F) :
    (W.veluQuotientOfSums t w).map f = (W.map f).veluQuotientOfSums (f t) (f w) := by
  ext <;> simp only [veluQuotientOfSums, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_b₂, map_sub, map_mul,
    map_ofNat]

end WeierstrassCurve.FullKernelQuotientBaseChange

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_map_fullKernelQuotient_mapPoint.WeierstrassCurve in

theorem solution {F K : Type*} [Field F] [Field K]
    [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F) (f : F →+* K) (Q : W.toAffine.Point)
    (N : ℕ) :
    (W.map f).fullKernelQuotient (mapPoint f Q) N = (W.fullKernelQuotient Q N).map f := by
  simp only [fullKernelQuotient]
  rw [FullKernelQuotientBaseChange.oddOrderSummingSet_mapPoint, FullKernelQuotientBaseChange.sum_image_prodMap,
    FullKernelQuotientBaseChange.sum_image_prodMap, FullKernelQuotientBaseChange.veluQuotientOfSums_map, map_sum,
    map_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun P _ => ?_
  · rw [Prod.map_fst, Prod.map_snd, FullKernelQuotientBaseChange.veluGx_map]
  · rw [Prod.map_fst, Prod.map_snd, map_sub, map_mul, map_mul, FullKernelQuotientBaseChange.veluGx_map,
      FullKernelQuotientBaseChange.veluGy_map]
