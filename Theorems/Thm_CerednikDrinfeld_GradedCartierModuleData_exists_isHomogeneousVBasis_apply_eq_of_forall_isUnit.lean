import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B}
    (q : S →+* B) (hq : Function.Surjective q) (hu : ∀ s : S, IsUnit (q s) → IsUnit s)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : DS.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DS D f)
    (β : Fin 2 → D.M) (hβ : D.IsHomogeneousVBasis β) :
    ∃ γ : Fin 2 → DS.M, DS.IsHomogeneousVBasis γ ∧ ∀ i : Fin 2, f (γ i) = β i := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit.solution
