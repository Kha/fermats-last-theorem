import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv
    {G : Type} [Group G] (H : Subgroup G) {R₀ P₀ : Rep ℤ ↥H} (f₀ : R₀ ⟶ P₀) (C : Rep ℤ G)
    (φ : (Rep.indFunctor ℤ H.subtype).obj R₀ ⟶ C) :
    (∃ χ : (Rep.indFunctor ℤ H.subtype).obj P₀ ⟶ C, (Rep.indFunctor ℤ H.subtype).map f₀ ≫ χ = φ) ↔
      ∃ χ₀ : P₀ ⟶ Rep.res H.subtype C, f₀ ≫ χ₀ = (Rep.indResAdjunction ℤ H.subtype).homEquiv R₀ C φ := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv.solution
