import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap
import P2M.Util
namespace P2MW.S_Rep_IsTateCupProduct_cup_neg_one_mk

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"
open groupCohomology

namespace P2mS26Hm1

noncomputable def tmulRight {k G : Type u} [CommRing k] [Group G] (M B : Rep.{u} k G) (b : B.ρ.invariants) :
    M ⟶ M ⊗ B :=
  Rep.ofHom ⟨(TensorProduct.mk k M B).flip (b : B), fun g => LinearMap.ext fun m => by
    change (M.ρ g m) ⊗ₜ[k] (b : B) = (M.ρ.tprod B.ρ) g (m ⊗ₜ[k] (b : B))
    rw [Representation.tprod_apply, TensorProduct.map_tmul, b.2 g]⟩

end P2mS26Hm1

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (x : A.tateHneg1) (a₀ : A) (hx : (x : A.ρ.Coinvariants) = Representation.Coinvariants.mk A.ρ a₀)
    (b : B.ρ.invariants) (z : (A ⊗ B).tateHneg1)
    (hz : (z : (A ⊗ B).ρ.Coinvariants) = Representation.Coinvariants.mk (A ⊗ B).ρ (a₀ ⊗ₜ[k] (b : B))) :
    cup A B (-1) 0 (-1) (add_zero (-1)) x (Submodule.Quotient.mk b : B.tateH0) = z := by
  refine (Rep.IsTateCupProduct.cup_mk_right_eq_tateMap hcup A B b (P2mS26Hm1.tmulRight A B b) (fun _ => rfl)
    (-1) (show A.tateCohomology (-1) from x)).trans (Subtype.ext ?_)
  change Rep.coinvariantsMap (P2mS26Hm1.tmulRight A B b) (x : A.ρ.Coinvariants) = (z : (A ⊗ B).ρ.Coinvariants)
  rw [hx, hz, Rep.coinvariantsMap_mk]
  rfl
