import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH

set_option autoImplicit false

theorem ModularForm.alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map (2 : ℤ) γ f = f)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hg : g ∈ CongruenceSubgroup.Gamma0 W.R)
    (hgH : ∃ u ∈ H,
      ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = CohCarrier.gamma0Units W.R ⟨g, hg⟩) :
    SlashAction.map (2 : ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ g)
        (ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f) =
      ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH.solution
