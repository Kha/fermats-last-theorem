import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv

set_option autoImplicit false
open CategoryTheory groupCohomology Rep

theorem groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (A : Rep k G) (B : Rep k H) (φ : A ≅ Rep.res e.toMonoidHom B) (n : ℕ) :
    ∃ ψ : groupCohomology A n ≃ₗ[k] groupCohomology B n,
      ∀ x : groupCohomology B n,
        ψ.symm x = (groupCohomology.map e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A) n).hom x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv.solution
