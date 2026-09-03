import Definitions.Def_CuspForm_LatticeHeckeFamily
import P2M.Util
import P2M.Sol.S_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient

theorem CuspForm.exists_injective_linearMap_torsionBySet_intLattice_quotient (N p : ℕ) [NeZero N]
    (m : Ideal ModularCurve.HeckeAlg) [m.IsMaximal] (hpm : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ m) :
    letI := (CuspForm.latticeHeckeFamily N).module
    ∃ a : Submodule.torsionBySet ModularCurve.HeckeAlg
        (↥(CuspForm.intLattice N 2) ⧸ (Ideal.span {((p : ℕ) : ModularCurve.HeckeAlg)} • (⊤ : Submodule ModularCurve.HeckeAlg ↥(CuspForm.intLattice N 2)))) m
          →ₗ[ModularCurve.HeckeAlg ⧸ m] (ModularCurve.HeckeAlg ⧸ m),
      Function.Injective a := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient.solution
