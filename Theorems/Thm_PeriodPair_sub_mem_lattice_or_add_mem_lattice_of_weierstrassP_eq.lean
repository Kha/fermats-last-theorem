import Mathlib
import P2M.Util
import P2M.Sol.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq
attribute [-simp] PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

set_option autoImplicit false

theorem PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (h : L.weierstrassP a = L.weierstrassP b) :
    a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq.solution
