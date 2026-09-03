import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
namespace P2MW.S_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1 (MonoidHom.id _) M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) := by
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1_iff (MonoidHom.id _) M x).1 hx
  have hcomp : (locRes (extArithLoc S) M v).hom ((H1π M).hom c)
      = (H1π (Rep.res (extArithLoc S v) M)).hom
          (mapCocycles₁ (extArithLoc S v) (𝟙 (Rep.res (extArithLoc S v) M)) c) :=
    H1π_comp_map_apply (extArithLoc S v) (𝟙 (Rep.res (extArithLoc S v) M)) c
  rw [hcomp]
  refine H1π_mem_continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) ?_
  obtain ⟨F, hF, hc⟩ := hc
  refine ⟨F, hF, fun h s hs => ?_⟩
  show c (extArithLoc S v (h * s)) = c (extArithLoc S v h)
  rw [map_mul]
  exact hc (extArithLoc S v h) (extArithLoc S v s) hs
