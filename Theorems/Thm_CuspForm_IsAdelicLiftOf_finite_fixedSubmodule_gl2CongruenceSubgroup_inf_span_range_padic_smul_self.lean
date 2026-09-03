import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv

theorem CuspForm.IsAdelicLiftOf.finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ)
    (n : ℕ) :
    Module.Finite ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n)
          (LocalNewvector.AdelicSpan Φ) ⊓
        Submodule.span ℂ
          (Set.range fun h : GL (Fin 2) ℚ_[q] => h • LocalNewvector.AdelicSpan.self Φ)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self.solution
