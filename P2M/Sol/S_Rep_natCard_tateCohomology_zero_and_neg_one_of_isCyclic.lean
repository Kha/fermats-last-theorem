import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_add_two
import P2M.Util
namespace P2MW.S_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    [IsCyclic G] (A : Rep.{u} k G) :
    Nat.card (A.tateCohomology 0) = Nat.card (groupCohomology A 2) ∧
      Nat.card (A.tateCohomology (-1)) = Nat.card (groupCohomology A 1) := by
  letI : CommGroup G := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨e0⟩ := Rep.nonempty_tateCohomology_iso_add_two A g hg 0
  obtain ⟨e1⟩ := Rep.nonempty_tateCohomology_iso_add_two A g hg (-1)
  exact ⟨Nat.card_congr e0.toLinearEquiv.toEquiv, Nat.card_congr e1.toLinearEquiv.toEquiv⟩
