import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_gamma1_hasNebentypus_hecke_eigen_of_adelicLift_fnTwist_of_mem_span_of_fixed
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_gamma1_hasNebentypus_hecke_eigen_of_adelicLift_fnTwist_of_mem_span_of_fixed
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (θ : ℤ_[q]ˣ →* ℂˣ)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ,
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y) :
    ∃ (N : ℕ) (_ : NeZero N) (ε : DirichletCharacter ℂ N) (F : CuspForm (CongruenceSubgroup.Gamma1 N) 2),
      q ∣ N ∧ (∀ r : ℕ, r.Prime → r ∣ N → r ∣ M ∨ r = q) ∧
      F ≠ 0 ∧ CuspForm.HasNebentypus ε F ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = ℓ →
        ε (ℓ : ZMod N) = ((θ u)⁻¹ : ℂˣ)) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff F (ℓ * n) +
            ε (ℓ : ZMod N) * (ℓ : ℂ) ^ ((2 : ℤ) - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0) =
          (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
            ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff F n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_gamma1_hasNebentypus_hecke_eigen_of_adelicLift_fnTwist_of_mem_span_of_fixed.solution
