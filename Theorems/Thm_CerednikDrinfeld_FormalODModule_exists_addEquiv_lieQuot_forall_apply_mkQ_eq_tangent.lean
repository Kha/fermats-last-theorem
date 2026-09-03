import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) :
    ∃ Λ : (X.toGradedCartierModuleData j hc).LieQuot ≃+ (Fin 2 → B),
      (∀ m : MvFormalGroup.CartierModule p X.F,
          Λ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = MvFormalGroup.CartierModule.tangent m) ∧
      (∀ (w : WittVector p B) (q : (X.toGradedCartierModuleData j hc).LieQuot),
          Λ (w • q) = w.coeff 0 • Λ q) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent.solution
