import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
import Theorems.Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom
import P2M.Util
namespace P2MW.S_CohCarrier_isParabolicHom_heckeT_top

set_option autoImplicit false

theorem solution (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (hφ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) φ) :
    ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) (CohCarrier.heckeT N ⊤ ℓ A φ) := by
  have hle : CongruenceSubgroup.Gamma0 N ≤ CohCarrier.GammaH N ⊤ := (CohCarrier.GammaH_top (M := N)).ge
  let ψ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A :=
    φ.comp (MonoidHom.toAdditive (Subgroup.inclusion hle))
  have hψ : ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) ψ :=
    fun δ hδ => hφ (Subgroup.inclusion hle δ) hδ
  intro γ hγ
  rw [CohCarrier.heckeT_top_apply_eq_heckeOperatorHom N ℓ A φ ψ (fun _ => rfl) γ]
  exact ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ A ψ hψ
    ⟨γ.1, CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩ hγ
