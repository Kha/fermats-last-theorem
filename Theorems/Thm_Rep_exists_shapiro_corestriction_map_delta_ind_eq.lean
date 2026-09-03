import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_shapiro_corestriction_map_delta_ind_eq

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_shapiro_corestriction_map_delta_ind_eq
    {G : Type} [Group G] [Fintype G] (H : Subgroup G)
    {T₀ : ShortComplex (Rep ℤ ↥H)} (hT₀ : T₀.ShortExact)
    (hT : (T₀.map (Rep.indFunctor ℤ H.subtype)).ShortExact) (C : Rep ℤ G) :
    ∃ (Sh : groupCohomology T₀.X₃ 1 →+ groupCohomology ((Rep.indFunctor ℤ H.subtype).obj T₀.X₃) 1)
      (cor : groupCohomology (Rep.res H.subtype C) 2 →+ groupCohomology C 2),
      (∀ x : groupCohomology C 2,
        cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype C)) 2).hom x) = H.index • x) ∧
      ∀ (φ : (Rep.indFunctor ℤ H.subtype).obj T₀.X₁ ⟶ C) (y₀ : groupCohomology T₀.X₃ 1),
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT 1 2 rfl).hom (Sh y₀)) =
          cor ((groupCohomology.map (MonoidHom.id ↥H) ((Rep.indResAdjunction ℤ H.subtype).homEquiv T₀.X₁ C φ) 2).hom
            ((groupCohomology.δ hT₀ 1 2 rfl).hom y₀)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_shapiro_corestriction_map_delta_ind_eq.solution
