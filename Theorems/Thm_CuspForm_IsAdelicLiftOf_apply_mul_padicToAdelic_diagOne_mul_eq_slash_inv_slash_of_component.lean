import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.IsAdelicLiftOf.apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (u : ℤ_[q]ˣ)
    (γ : SL(2, ℤ)) (hγM : γ ∈ CongruenceSubgroup.Gamma M')
    (hγq : ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) =
      ((CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) *
          LocalNewvector.gl2ReductionHom q k *
          (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom
            (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))⁻¹ : CuspidalType.GL2 q) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) i j)
    (F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom
                    (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))) =
              ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          (LocalNewvector.AdelicSpan.toFn Φ y).toFn
              (h * AdelicDock.padicToAdelic q
                (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) *
                  (k : GL (Fin 2) ℚ_[q]))) =
            (((⇑F) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h)
              UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component.solution
