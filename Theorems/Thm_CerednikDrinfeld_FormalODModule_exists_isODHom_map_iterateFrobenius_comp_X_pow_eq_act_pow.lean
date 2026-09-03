import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow
    {p : ℕ} [Fact p.Prime] {κ : Type u} [Field κ] [CharP κ p]
    (Φ : FormalODModule p κ) (hΦ4 : Φ.HasHeight 4) (m : ℕ) :
    ∃ V : Series κ,
      FormalODModule.IsODHom (Φ.map (iterateFrobenius κ p m)) Φ V ∧
      V.comp (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ (p ^ m)) =
        Φ.act ((p : Zp2 p) ^ m) ∧
      FormalODModule.HasKernelOfDegree V (p ^ (2 * m)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow.solution
