import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
namespace P2MW.S_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice

noncomputable section

open ModularForm ModularFormClass

p2m_open "CuspForm ModularForm.CuspForm"

theorem solution {N : ℕ} {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) (h : ∀ f ∈ CuspForm.intLattice N k, t f = 0) : t = 0 :=
  LinearMap.ext_on hN fun f hf => by rw [LinearMap.zero_apply]; exact h f hf

end
