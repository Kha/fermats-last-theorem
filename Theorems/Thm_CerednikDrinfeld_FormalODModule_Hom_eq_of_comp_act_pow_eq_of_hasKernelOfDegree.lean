import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.Hom.eq_of_comp_act_pow_eq_of_hasKernelOfDegree
    {q : ℕ} [Fact q.Prime] {B : Type u} [CommRing B] [IsNoetherianRing B]
    {X X' : FormalODModule q B} (k d : ℕ)
    (hk : FormalODModule.HasKernelOfDegree (X.act (((q : ℕ) : Zp2 q) ^ k)) d)
    (ψ ψ' : FormalODModule.Hom X X')
    (h : ψ.toSeries.comp (X.act (((q : ℕ) : Zp2 q) ^ k)) = ψ'.toSeries.comp (X.act (((q : ℕ) : Zp2 q) ^ k))) :
    ψ = ψ' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree.solution
