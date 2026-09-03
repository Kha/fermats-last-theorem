import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.card_le_finrank_modPCusp_of_linearIndependent
    (N : ℕ) [NeZero N] (k : ℤ) (F : Type) [Field F] {ι : Type} [Fintype ι]
    (f : ι → CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ι → ℕ → ℤ)
    (hf : ∀ i n, ModularFormClass.qCoeff (f i) n = (a i n : ℂ))
    (hli : LinearIndependent ℂ f) :
    Fintype.card ι ≤ Module.finrank F ↥(ModPForms.modPCusp N k F) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.solution
