import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0 {k G : Type u} [CommRing k] [Group G] {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (a : groupCohomology.cocycles₁ A) :
    (φ.hom ∘ a) ∈ groupCohomology.coboundaries₁ B ↔
      ∃ c ∈ C.ρ.invariants, ((a : G → A) - groupCohomology.deltaCochain₀ φ ψ hψ c) ∈ groupCohomology.coboundaries₁ A := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0.solution
