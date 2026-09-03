import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_ConductorDatum
import P2M.Util
import P2M.Sol.S_CuspForm_HasNebentypus_apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1

set_option autoImplicit false

theorem CuspForm.HasNebentypus.apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (q : ℕ) [Fact q.Prime] (u : ℤ_[q]ˣ) (d : ℤ)
    (hdq : (d : ℤ_[q]) * u - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ M.factorization q})
    (hdM : ((M / q ^ M.factorization q : ℕ) : ℤ) ∣ d - 1)
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q
          (LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
      ε (d : ZMod M) * Φ x := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasNebentypus_apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1.solution
