import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularCurve_X1HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good
    (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)
    (hΛ : ∀ c : ℤ_[p],
      Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c)
    (G : Set ModularCurve.HeckeAlgOne)
    (hsep : ∀ w ∈ Algebra.adjoin ℤ G, ∃ P : Polynomial ℤ, P ≠ 0 ∧ (P.map (Int.castRingHom ℚ)).Separable ∧
      Polynomial.aeval (ModularCurve.tateHeckeRepOne p J w) P = 0)
    (hgood : ∀ t : ModularCurve.HeckeAlgOne, ∃ s ∈ Algebra.adjoin ℤ G, ∃ u ∈ Algebra.adjoin ℤ G,
      Λ ⟨ModularCurve.rationalHeckeRepOne p J s,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J s⟩ ≠ 0 ∧
      ModularCurve.tateHeckeRepOne p J s * ModularCurve.tateHeckeRepOne p J t = ModularCurve.tateHeckeRepOne p J u) :
    (⨅ t : ModularCurve.HeckeAlgOne,
        LinearMap.ker ((ModularCurve.tateHeckeRepOne p J t).baseChange K - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • LinearMap.id)) ⊓
      Submodule.span K
        {z : K ⊗[ℤ_[p]] TateModule p J |
          ∃ (t : ModularCurve.HeckeAlgOne) (y : K ⊗[ℤ_[p]] TateModule p J),
            z = (ModularCurve.tateHeckeRepOne p J t).baseChange K y - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • y} = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_inf_span_eq_bot_of_separable_of_good.solution
