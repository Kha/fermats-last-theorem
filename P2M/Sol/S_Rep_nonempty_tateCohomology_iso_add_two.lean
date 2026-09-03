import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_nonempty_tateH0_linearEquiv_homology_normHomCompSub
import Theorems.Thm_Rep_nonempty_tateHneg1_linearEquiv_homology_subCompNormHom
import P2M.Util
namespace P2MW.S_Rep_nonempty_tateCohomology_iso_add_two

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (q : ℤ) :
    Nonempty (A.tateCohomology q ≅ A.tateCohomology (q + 2)) := by
  classical

  obtain ⟨e0⟩ := Rep.nonempty_tateH0_linearEquiv_homology_normHomCompSub A g hg
  obtain ⟨e1⟩ := Rep.nonempty_tateHneg1_linearEquiv_homology_subCompNormHom A g hg
  rcases q with (_ | n) | (_ | _ | _ | n)
  ·
    exact ⟨e0.toModuleIso ≪≫ (FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm⟩
  ·
    show Nonempty (groupCohomology A (n + 1) ≅ groupCohomology A (n + 1 + 2))
    rcases Nat.even_or_odd (n + 1) with hn | hn
    · exact ⟨FiniteCyclicGroup.groupCohomologyIsoEven A g hg (n + 1) hn ≪≫
        (FiniteCyclicGroup.groupCohomologyIsoEven A g hg (n + 1 + 2) (hn.add even_two)).symm⟩
    · exact ⟨FiniteCyclicGroup.groupCohomologyIsoOdd A g hg (n + 1) hn ≪≫
        (FiniteCyclicGroup.groupCohomologyIsoOdd A g hg (n + 1 + 2) (hn.add_even even_two)).symm⟩
  ·
    exact ⟨e1.toModuleIso ≪≫ (FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm⟩
  ·
    exact ⟨FiniteCyclicGroup.groupHomologyIsoOdd A g hg 1 odd_one ≪≫ e0.toModuleIso.symm⟩
  ·
    exact ⟨FiniteCyclicGroup.groupHomologyIsoEven A g hg 2 even_two ≪≫ e1.toModuleIso.symm⟩
  ·
    show Nonempty (groupHomology A (n + 1 + 2) ≅ groupHomology A (n + 1))
    rcases Nat.even_or_odd (n + 1) with hn | hn
    · exact ⟨FiniteCyclicGroup.groupHomologyIsoEven A g hg (n + 1 + 2) (hn.add even_two) ≪≫
        (FiniteCyclicGroup.groupHomologyIsoEven A g hg (n + 1) hn).symm⟩
    · exact ⟨FiniteCyclicGroup.groupHomologyIsoOdd A g hg (n + 1 + 2) (hn.add_even even_two) ≪≫
        (FiniteCyclicGroup.groupHomologyIsoOdd A g hg (n + 1) hn).symm⟩
