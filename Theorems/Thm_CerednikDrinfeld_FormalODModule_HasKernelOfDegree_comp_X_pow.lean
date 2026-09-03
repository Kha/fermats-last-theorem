import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_X_pow
    {B : Type u} [CommRing B] {φ : Series B} {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d)
    {q : ℕ} (hq : q ≠ 0) :
    FormalODModule.HasKernelOfDegree (φ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q)
      (d * q ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow.solution
