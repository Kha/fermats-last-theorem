import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_finrank_iInf_eigenspace_baseChange_eq

theorem Module.End.finrank_iInf_eigenspace_baseChange_eq
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι : Type*} (T : ι → Module.End F W) (c : ι → F) :
    Module.finrank L ↥(⨅ i, Module.End.eigenspace ((T i).baseChange L) (algebraMap F L (c i))) =
      Module.finrank F ↥(⨅ i, Module.End.eigenspace (T i) (c i)) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_finrank_iInf_eigenspace_baseChange_eq.solution
