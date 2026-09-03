import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false

universe u

theorem MvFormalGroup.mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ} (F : MvFormalGroup n k)
    (g : MvPowerSeries (Fin n) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hglin : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) g = 0)
    (hprim : F.addCoboundary g ∈ Ideal.span (Set.range fun s : Fin n ⊕ Fin n =>
      (MvPowerSeries.X s : MvPowerSeries (Fin n ⊕ Fin n) k) ^ p)) :
    g ∈ Ideal.span (Set.range fun i : Fin n => (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ p) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero.solution
