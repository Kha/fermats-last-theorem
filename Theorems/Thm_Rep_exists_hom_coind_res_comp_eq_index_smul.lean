import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_hom_coind_res_comp_eq_index_smul

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_hom_coind_res_comp_eq_index_smul {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.FiniteIndex] (N : Rep.{u} k G) :
    ∃ (ι : N ⟶ Rep.coind S.subtype (Rep.res S.subtype N)) (τ : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ N),
      (∀ (n : N) (g : G), ((ι.hom n : Rep.coind S.subtype (Rep.res S.subtype N)) : G → N) g = N.ρ g n) ∧
      (∀ f : Rep.coind S.subtype (Rep.res S.subtype N),
        τ.hom f = ∑ᶠ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹)) ∧
      Function.Surjective τ.hom ∧
      ∀ n : N, τ.hom (ι.hom n) = (S.index : k) • n := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_hom_coind_res_comp_eq_index_smul.solution
