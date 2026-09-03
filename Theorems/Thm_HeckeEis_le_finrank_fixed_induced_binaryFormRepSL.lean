import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.le_finrank_fixed_induced_binaryFormRepSL (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n)
    (W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)))
    (hW : ∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) :
    Module.finrank ℂ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) = (n + 1) * (CongruenceSubgroup.Gamma0 N).index ∧
    2 * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        * Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n ModularGroup.S - 1)))
      + ((CongruenceSubgroup.Gamma0 N).index - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}) * (n + 1)
      ≤ 2 * Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ - 1)) ∧
    3 * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // (ModularGroup.S * ModularGroup.T) • x = x}
        * Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.S * ModularGroup.T) - 1)))
      + ((CongruenceSubgroup.Gamma0 N).index - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // (ModularGroup.S * ModularGroup.T) • x = x}) * (n + 1)
      ≤ 3 * Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ - 1)) ∧
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
      ≤ Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.T, Subgroup.mem_top _⟩ - 1)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.solution
