import Mathlib
import P2M.Util
namespace P2MW.S_Rep_invariants_res_eq_invariants_res_range

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical TensorProduct

theorem solution
    {k : Type} [CommRing k] {G D' : Type} [Group G] [Group D'] (φ : D' →* G) (X : Rep.{0} k G) :
    (Rep.res φ X).ρ.invariants = (Rep.res φ.range.subtype X).ρ.invariants := by
  ext v
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  constructor
  · rintro h ⟨g, d, rfl⟩
    exact h d
  · intro h d
    exact h ⟨φ d, d, rfl⟩
