import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_SlashInvariantForm_coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem SlashInvariantForm.coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ))]
    {k : ℤ} {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [SlashInvariantFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (⇑(SlashInvariantForm.trace
        (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ)) f) :
        UpperHalfPlane → ℂ) =
      ⇑f + ModularForm.heckeU k p ((⇑f : UpperHalfPlane → ℂ) ∣[k] W.alGL⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_SlashInvariantForm_coe_trace_gammaH_eq_add_heckeU_slash_alGL_inv.solution
