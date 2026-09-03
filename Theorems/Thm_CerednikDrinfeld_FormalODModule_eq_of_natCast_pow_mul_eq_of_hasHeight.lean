import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.eq_of_natCast_pow_mul_eq_of_hasHeight
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) {h : ℕ} (hX : X.HasHeight h) (d : ℕ) (x y : MvFormalGroup.End X.F)
    (hxy : ((p ^ d : ℕ) : MvFormalGroup.End X.F) * x = ((p ^ d : ℕ) : MvFormalGroup.End X.F) * y) : x = y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight.solution
