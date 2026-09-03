import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeT
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU
import P2M.Util
namespace P2MW.S_CuspForm_mem_intLattice_of_mem_heckeAlgebra

noncomputable section

open ModularForm ModularFormClass

p2m_open "CuspForm ModularForm.CuspForm"

theorem solution {N : ℕ} [NeZero N] {k : ℤ} (hk : 1 ≤ k) {S : Set ℕ} {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)} (ht : t ∈ CuspForm.heckeAlgebra N k S) {f : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hf : f ∈ CuspForm.intLattice N k) : t f ∈ CuspForm.intLattice N k := by
  revert f
  refine Algebra.adjoin_induction (p := fun t _ => ∀ {f}, f ∈ intLattice N k → t f ∈ intLattice N k)
    ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩) f hf
    · exact CuspForm.mem_intLattice_of_coe_eq_heckeT hk hℓ.ne_zero (CuspForm.coe_heckeTLin_apply k hℓ hℓN f) hf
    · exact CuspForm.mem_intLattice_of_coe_eq_heckeU hq.ne_zero (CuspForm.coe_heckeULin_apply k hqN f) hf
  · intro r f hf
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact (intLattice N k).smul_mem r hf
  · intro x y _ _ hx hy f hf
    rw [LinearMap.add_apply]
    exact add_mem (hx hf) (hy hf)
  · intro x y _ _ hx hy f hf
    rw [Module.End.mul_apply]
    exact hx (hy hf)

end
