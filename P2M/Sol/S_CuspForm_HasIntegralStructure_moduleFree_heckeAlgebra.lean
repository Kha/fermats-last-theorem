import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import P2M.Util
namespace P2MW.S_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra

noncomputable section

open ModularForm ModularFormClass

p2m_open "CuspForm ModularForm.CuspForm"

theorem solution {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) : Module.Free ℤ (CuspForm.heckeAlgebra N k S) := by
  haveI := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN hk S
  infer_instance

end
