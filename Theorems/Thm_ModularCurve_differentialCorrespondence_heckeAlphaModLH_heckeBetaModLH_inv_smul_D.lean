import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D

set_option autoImplicit false

theorem ModularCurve.differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hsep : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      AlgebraicCurve.SeparableAlong K (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ))
    (f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ) (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ))
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ f))⁻¹ •
        KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ f)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D.solution
