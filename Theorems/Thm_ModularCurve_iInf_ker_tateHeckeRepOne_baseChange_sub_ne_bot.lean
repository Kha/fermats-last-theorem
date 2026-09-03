import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot
    (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)
    (hΛ : ∀ c : ℤ_[p],
      Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c) :
    (⨅ t : ModularCurve.HeckeAlgOne,
        LinearMap.ker ((ModularCurve.tateHeckeRepOne p J t).baseChange K - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • LinearMap.id)) ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot.solution
