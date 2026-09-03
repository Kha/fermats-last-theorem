import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import P2M.Util
import Definitions.Def_Compat_Mathlib430
namespace P2MW.S_ModularCurve_JZero_invariants_le_invariants_of_le

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N]
    (K L' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L') :
    JZero N ^+ ↥K.fixingSubgroup ≤ JZero N ^+ ↥L'.fixingSubgroup := by
  intro x hx
  rw [FixedPoints.mem_addSubgroup] at hx ⊢
  intro σ
  exact hx ⟨σ.1, IntermediateField.fixingSubgroup_le hKL σ.2⟩
