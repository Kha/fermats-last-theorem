import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_ExtCitation_CyclotomicUnits
import Theorems.Thm_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units
import Theorems.Thm_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot
import Theorems.Thm_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow
import P2M.Util
namespace P2MW.S_ExtCitation_extVanishingCts_of_five_le

set_option autoImplicit false

open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
open ExtCitation ExtCitation.Cyclotomic

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ExtCitation.ExtVanishingCts p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact extVanishingCts_of_e2ClassGroup_and_e2Units p hp5
    (unitsGalAction p)
    (fun d u => unitsEnd_proj p (clRingAction p (CyclotomicField p ℚ) d) u)
    (clGalAction_omegaEigenspace_two_eq_bot p hp5)
    (fun u heig hloc =>
      unitsOmegaEigenvector_two_eq_zero_of_local_pow p hp5 u heig hloc)
