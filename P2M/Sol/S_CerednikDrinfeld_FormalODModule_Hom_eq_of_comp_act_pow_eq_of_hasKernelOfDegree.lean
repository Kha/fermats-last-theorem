import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {q : ℕ} [Fact q.Prime] {B : Type u} [CommRing B] [IsNoetherianRing B]
    {X X' : FormalODModule q B} (k d : ℕ)
    (hk : FormalODModule.HasKernelOfDegree (X.act (((q : ℕ) : Zp2 q) ^ k)) d)
    (ψ ψ' : FormalODModule.Hom X X')
    (h : ψ.toSeries.comp (X.act (((q : ℕ) : Zp2 q) ^ k)) = ψ'.toSeries.comp (X.act (((q : ℕ) : Zp2 q) ^ k))) :
    ψ = ψ' := by
  apply FormalODModule.Hom.ext
  funext i
  exact CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree (X.act (((q : ℕ) : Zp2 q) ^ k))
    (X.isLawHom_act _).1 hk (ψ.toSeries i) (ψ'.toSeries i) (congrFun h i)
