import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

set_option autoImplicit false

theorem CuspForm.HasNebentypus.qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
    (hε : CuspForm.HasNebentypus ε F)
    (Ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΨ : CuspForm.IsAdelicLiftOfGamma1 F Ψ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (lam : ℂ)
    (heig : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          ∑ i : Fin (ℓ + 1), Ψ (h * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) = lam * Ψ h)
    (n : ℕ) :
    ModularFormClass.qCoeff F (ℓ * n) +
        ε (ℓ : ZMod N) * (ℓ : ℂ) ^ ((2 : ℤ) - 1) *
          (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0) =
      ε (ℓ : ZMod N) * lam * ModularFormClass.qCoeff F n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasNebentypus_qCoeff_hecke_eq_of_isAdelicLiftOfGamma1_of_sum_apply_padicToAdelic_eq.solution
