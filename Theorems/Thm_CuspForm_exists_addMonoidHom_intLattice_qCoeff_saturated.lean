import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_QCoeffLinear
import P2M.Util
import P2M.Sol.S_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ a : ↥(CuspForm.intLattice N k) →+ (ℕ → ℤ),
      (∀ (f : ↥(CuspForm.intLattice N k)) (n : ℕ),
        ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) n) ∧
      Function.Injective a ∧
      ∀ (m : ℤ) (f : ↥(CuspForm.intLattice N k)), (∀ n, m ∣ a f n) →
        ∃ g : ↥(CuspForm.intLattice N k), f = m • g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated.solution
