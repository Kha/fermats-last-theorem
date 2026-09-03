import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_intLattice_fg
import P2M.Util
namespace P2MW.S_CuspForm_intLattice_free_and_finite

namespace CuspForm p2m_export "CuspForm" "intLattice intLattice_fg" end CuspForm
p2m_open_scoped "CuspForm" in

theorem CuspForm.intLattice_free_and_finite' (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Free ℤ (CuspForm.intLattice N k) ∧ Module.Finite ℤ (CuspForm.intLattice N k) := by
  haveI : Module.Finite ℤ (CuspForm.intLattice N k) := Module.Finite.iff_fg.mpr (CuspForm.intLattice_fg N k)
  haveI : NoZeroSMulDivisors ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
    ⟨fun {c x} h => by
      rw [← Int.cast_smul_eq_zsmul ℂ c x] at h
      rcases smul_eq_zero.mp h with h1 | h1
      · exact Or.inl (Int.cast_eq_zero.mp h1)
      · exact Or.inr h1⟩
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

theorem solution (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Free ℤ (CuspForm.intLattice N k) ∧ Module.Finite ℤ (CuspForm.intLattice N k) :=
  CuspForm.intLattice_free_and_finite' N k
