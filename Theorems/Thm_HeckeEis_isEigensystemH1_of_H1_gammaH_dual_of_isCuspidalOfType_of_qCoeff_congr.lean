import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one Deformation.matrixRepresentation_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false
open CongruenceSubgroup Polynomial

theorem
HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
    (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime]
    (g : CuspForm (Gamma0 (N * q ^ 2)) 2) (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ) (hθ : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V))
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    (H₁ : Subgroup (ZMod (N * q ^ 2))ˣ)
    (hH₁ : H₁ = (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)
    (conj : ↥red.ker →* ↥(CohCarrier.GammaH (N * q ^ 2) H₁))
    (hconj : ∀ x : ↥red.ker,
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 = ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
      (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
        (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1)
    (φ : CohCarrier.H1 (N * q ^ 2) H₁
        (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)))
    (hφ0 : φ ≠ 0)
    (hφeq : ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker),
        φ (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
          (LocalNewvector.gl2ReductionRep q V).dual (red γ) (φ (Additive.ofMul (conj ⟨y, hy⟩))))
    (hφT : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ((LocalNewvector.gl2ReductionRep q V).dual
            (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))).toAddMonoidHom.comp
          (CohCarrier.heckeT (N * q ^ 2) H₁ ℓ
            (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) φ) =
          ModularFormClass.qCoeff g ℓ • φ)
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (𝔪 : Ideal (integralClosure ℤ ℂ))
    (red𝔪 : integralClosure ℤ ℂ →+* κ) (hker𝔪 : RingHom.ker red𝔪 = 𝔪)
    (S₀ : Set ℕ) (hqS₀ : q ∈ S₀) (b : ℕ → ℤ)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ℓ ∉ S₀ →
      ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff g ℓ ∧ c - (b ℓ : integralClosure ℤ ℂ) ∈ 𝔪)
    (hθ1 : θ ≠ 1) (hθp : ∃ n : ℕ, θ ^ p ^ n = 1)
:
    ∃ (Vσ : Type) (_ : AddCommGroup Vσ) (_ : Module κ Vσ) (_ : FiniteDimensional κ Vσ)
      (σ : Representation κ (CuspidalType.GL2 q) Vσ),
      (∀ g' : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g') = (X - 1) ^ 2 * LinearMap.charpoly (σ g')) ∧
      HeckeEis.IsEigensystemH1 N (σ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then σ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr.solution
