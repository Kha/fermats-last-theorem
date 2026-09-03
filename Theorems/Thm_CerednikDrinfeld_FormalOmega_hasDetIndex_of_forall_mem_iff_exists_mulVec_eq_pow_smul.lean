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
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul
    (p : ℕ) [Fact p.Prime] (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (u : ℤ_[p]ˣ) (e h : ℕ)
    (hγ : γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h)
    (N : Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN : ∀ v : Fin 2 → ℚ_[p], v ∈ N ↔
      ∃ (m : ℕ) (w c : Fin 2 → ℤ_[p]),
        (p : ℚ_[p]) ^ m • v = (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ∧
          γ.mulVec w = (p : ℤ_[p]) ^ (e + m) • c) :
    FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N (2 * (e : ℤ) - (h : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul.solution
