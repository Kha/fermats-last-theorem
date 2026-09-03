import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_corestriction_map_map_res_eq_map_norm
    {k G : Type} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex] [Fintype (G ⧸ S)]
    (C : Rep k G) (n : ℕ) :
    ∃ cor : groupCohomology (Rep.res S.subtype C) n →+ groupCohomology C n,
      ∀ (R : Rep k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C)
        (Nφ : R ⟶ C)
        (_ : ∀ x : R, Nφ.hom x = ∑ g : G ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)))
        (z : groupCohomology R n),
        cor ((groupCohomology.map (MonoidHom.id ↥S) φ n).hom
              ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n).hom z))
          = (groupCohomology.map (MonoidHom.id G) Nφ n).hom z := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm.solution
