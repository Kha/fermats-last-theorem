import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    (L L' : Rep ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (h : ∀ H : Subgroup G, Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L') 0)) :
    ∃ f : L ⟶ L', Function.Injective f.hom ∧ (f.hom : L →+ L').range.FiniteIndex := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq.solution
