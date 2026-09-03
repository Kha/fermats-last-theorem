import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_TwoChartCech_Sections_finite_H1_of_chartFinite

universe u

theorem TwoChartCech.Sections.finite_H1_of_chartFinite
    {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, u} R} (S : TwoChartCech.Sections.{u, u, u} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1) :
    Module.Finite R S.H1 := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Sections_finite_H1_of_chartFinite.solution
