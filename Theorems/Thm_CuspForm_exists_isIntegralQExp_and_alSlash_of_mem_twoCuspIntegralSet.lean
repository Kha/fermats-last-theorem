import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isIntegralQExp_and_alSlash_of_mem_twoCuspIntegralSet

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.exists_isIntegralQExp_and_alSlash_of_mem_twoCuspIntegralSet
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    (∃ pf : PowerSeries ℤ, ModularCurve.IsIntegralQExp f pf) ∧
      ∃ pfW : PowerSeries ℤ, ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isIntegralQExp_and_alSlash_of_mem_twoCuspIntegralSet.solution
