import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ

theorem ModularCurve.arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
    (q N : ℕ) [NeZero N] (K : Type*) [Field K] [Fact q.Prime] [CharP K q] [PerfectField K]
    (ι ι' : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (hj : ι' ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩))
    (hjN : ι' ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩))
    (w w' : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))
    (hw : ∀ x, x ∈ w.toValuationSubring ↔ 0 ≤ (ι x).order)
    (hw' : ∀ x, x ∈ w'.toValuationSubring ↔ 0 ≤ (ι' x).order) :
    ModularCurve.arithFrobC q K N • w = w' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ.solution
