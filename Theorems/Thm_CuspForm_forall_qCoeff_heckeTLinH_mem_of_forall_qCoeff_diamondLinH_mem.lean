import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : Subring ℂ)
    (hdia : ∀ (d : (ZMod M)ˣ) (g : CuspForm (CohCarrier.GammaH M H) 2),
      (∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(g)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(g)) n ∈ A) →
      ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d g)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 d g)) n ∈ A)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(f)) n ∈ A) :
    ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH 2 hℓ hℓM f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.heckeTLinH 2 hℓ hℓM f)) n ∈ A := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem.solution
