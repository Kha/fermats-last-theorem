import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModPForms.eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
    (p : ℕ) (hp : p.Prime) (N : ℕ) (hpN : ¬ p ∣ N) (k : ℤ)
    (F : Type) [Field F] (hpF : (p : F) ≠ 0)
    (ψ : PowerSeries F) (hψ : ψ ∈ ModPForms.modPCusp N k F)
    (hV : (PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) ψ else 0) ∈ ModPForms.modPCusp N k F) :
    ψ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp.solution
