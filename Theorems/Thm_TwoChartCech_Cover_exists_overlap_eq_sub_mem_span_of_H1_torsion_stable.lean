import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import P2M.Util
import P2M.Sol.S_TwoChartCech_Cover_exists_overlap_eq_sub_mem_span_of_H1_torsion_stable

universe u v

theorem TwoChartCech.Cover.exists_overlap_eq_sub_mem_span_of_H1_torsion_stable
    {R : Type u} [CommRing R] (𝒰 : TwoChartCech.Cover.{u, v} R) (p : R) (n : ℕ)
    (htors : ∀ x : 𝒰.structureSheaf.H1, p ^ (n + 1) • x = 0 → p ^ n • x = 0)
    (c0 : 𝒰.A0) (c1 : 𝒰.A1)
    (h0 : c0 * c0 - c0 ∈ Ideal.span {algebraMap R 𝒰.A0 p})
    (h1 : c1 * c1 - c1 ∈ Ideal.span {algebraMap R 𝒰.A1 p})
    (h01 : 𝒰.ρ0 c0 - 𝒰.ρ1 c1 ∈ Ideal.span {algebraMap R 𝒰.A01 p}) :
    ∃ (a0 : 𝒰.A0) (a1 : 𝒰.A1), 𝒰.ρ0 a0 = 𝒰.ρ1 a1 ∧
      a0 - c0 ∈ Ideal.span {algebraMap R 𝒰.A0 p} ∧ a1 - c1 ∈ Ideal.span {algebraMap R 𝒰.A1 p} := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Cover_exists_overlap_eq_sub_mem_span_of_H1_torsion_stable.solution
