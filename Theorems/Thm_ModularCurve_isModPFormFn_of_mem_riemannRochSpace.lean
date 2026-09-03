import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import P2M.Util
import P2M.Sol.S_ModularCurve_isModPFormFn_of_mem_riemannRochSpace

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.isModPFormFn_of_mem_riemannRochSpace
    (K : Type) [Field K] (N : ℕ) [NeZero N] (m : ℕ)
    [FiniteDimensional
      ↥(IntermediateField.adjoin K ({(⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))} :
        Set ↥(modularFunctionFieldFullC K N))) ↥(modularFunctionFieldFullC K N)]
    [Algebra.IsSeparable
      ↥(IntermediateField.adjoin K ({(⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))} :
        Set ↥(modularFunctionFieldFullC K N))) ↥(modularFunctionFieldFullC K N)]
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0))
    (G : ↥(modularFunctionFieldFullC K N)) (hG : G ∈ riemannRochSpace D) :
    IsModPFormFn K m (G : LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isModPFormFn_of_mem_riemannRochSpace.solution
