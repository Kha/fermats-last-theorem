import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_map_conj_eq_id

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.map_conj_eq_id
    {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (g : G) (n : ℕ)
    (φ : Rep.res (MulAut.conj g).toMonoidHom M ⟶ M)
    (hφ : ∀ m : Rep.res (MulAut.conj g).toMonoidHom M, φ.hom m = M.ρ g⁻¹ m) :
    groupCohomology.map (MulAut.conj g).toMonoidHom φ n = 𝟙 (groupCohomology M n) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_conj_eq_id.solution
