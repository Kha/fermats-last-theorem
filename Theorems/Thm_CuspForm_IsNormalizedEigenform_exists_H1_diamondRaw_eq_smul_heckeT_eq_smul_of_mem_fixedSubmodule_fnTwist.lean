import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.Padics.RingHoms
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist
    {L : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 L) 2} (hg : g.IsNormalizedEigenform)
    (q : ℕ) [Fact q.Prime] (hq2 : L.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy0 : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 1)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
      ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
              (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y) :
    ∃ φ : CohCarrier.H1 (L / q) ⊥ ℂ, φ ≠ 0 ∧
      φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH (L / q) ⊥) ℂ ∧
      (∀ (σ : CongruenceSubgroup.Gamma0 (L / q)) (u : ℤ_[q]ˣ),
        ((u : ℤ_[q]) : ℚ_[q]) =
            ((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) →
          CohCarrier.diamondRaw (L / q) ⊥ ℂ σ φ =
            ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
                (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
                  (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
                    (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2)⁻¹ • φ) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (L / q) ⊥ ℓ ℂ φ =
          ((η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) *
            ModularFormClass.qCoeff g ℓ) • φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist.solution
