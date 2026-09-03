import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exists_hom_dimShiftDownObj_trivial_leftRegular {k G : Type u} [CommRing k] [Group G] :
    ∃ j : (Rep.trivial k G k).dimShiftDownObj ⟶ Rep.leftRegularFinsupp k G,
      Function.Injective j.hom ∧
      (∀ x, Finsupp.linearCombination k (fun _ : G => (1 : k)) (j.hom x) = 0) ∧
      (∀ f : G →₀ k, Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0 → f ∈ LinearMap.range j.hom.toLinearMap) ∧
      (∀ g : G, ∃ d : (Rep.trivial k G k).dimShiftDownObj, j.hom d = Finsupp.single g 1 - Finsupp.single 1 1) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular.solution
