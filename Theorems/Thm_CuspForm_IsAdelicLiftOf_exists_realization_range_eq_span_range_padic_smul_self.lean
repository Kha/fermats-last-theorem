import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_exists_realization_range_eq_span_range_padic_smul_self
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.exists_realization_range_eq_span_range_padic_smul_self
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) V)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V)
      (_ : FiniteDimensional ℂ
        ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
      (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) ∧ Function.Injective f ∧
      LinearMap.range f =
        Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_exists_realization_range_eq_span_range_padic_smul_self.solution
