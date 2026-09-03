import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_goodEigensystemOccursAt_of_adelicLift_of_mem_span_of_fixed
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.goodEigensystemOccursAt_of_adelicLift_of_mem_span_of_fixed
    {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (a : ℕ) (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan Φ))
    (hcent : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y) :
    g.GoodEigensystemOccursAt (M / q ^ (M.factorization q - a)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_goodEigensystemOccursAt_of_adelicLift_of_mem_span_of_fixed.solution
