import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) 2, (⇑g : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH.solution
