import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_of_latticeRel
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S} (E : GradedCartierModuleData p S jS)
    (n : ℕ) (r : (Fin 2 → ℤ_[p]) →+ E.NMod) (v : Fin 2 → ℚ_[p]) (ζ ζ' : E.NMod)
    (h : Rigidified.LatticeRel E n r ζ v) (h' : Rigidified.LatticeRel E n r ζ' v) :
    ∃ N : ℕ, p ^ N • ζ = p ^ N • ζ' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel.solution
