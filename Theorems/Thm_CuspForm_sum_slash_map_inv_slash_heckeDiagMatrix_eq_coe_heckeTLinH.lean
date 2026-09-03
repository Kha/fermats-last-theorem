import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M')
    (t : Fin ℓ → ℤ) (htq : ∀ i, (q : ℤ) ∣ t i) (htℓ : Function.Injective fun i => ((t i : ℤ) : ZMod ℓ))
    (γ : Fin ℓ → GL (Fin 2) ℚ)
    (hγ : ∀ i, ((γ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t i : ℚ); 0, 1])
    (σ : SL(2, ℤ)) (hσb : (q : ℤ) ∣ σ 0 1) (hσc : ((q * M' * ℓ : ℕ) : ℤ) ∣ σ 1 0)
    (hσa : ((σ 0 0 : ℤ) : ZMod q) = (ℓ : ZMod q))
    (γinf : GL (Fin 2) ℚ)
    (hγinf : ((γinf : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)])
    (f : UpperHalfPlane → ℂ)
    (F' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (hF' : ⇑F' = f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    ((∑ i, f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (γ i)⁻¹) +
        f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γinf⁻¹) ∣[(2 : ℤ)]
        ModularForm.heckeDiagMatrix q =
      ⇑(CuspForm.heckeTLinH 2 hℓ hℓN F') := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.solution
