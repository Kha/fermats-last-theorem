import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_monoidHom_subgroupOf_conj_smul_and_hom_res_apply

set_option autoImplicit false
open CategoryTheory
open scoped Pointwise

theorem Rep.exists_monoidHom_subgroupOf_conj_smul_and_hom_res_apply
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H D : Subgroup G) (g : G) :
    ∃ (c : ↥((MulAut.conj g • H).subgroupOf D) →* ↥H)
      (T : Rep.res c (Rep.res H.subtype A) ⟶ Rep.res ((MulAut.conj g • H).subgroupOf D).subtype (Rep.res D.subtype A)),
      (∀ x : ↥((MulAut.conj g • H).subgroupOf D), ((c x : ↥H) : G) = g⁻¹ * ((x : ↥D) : G) * g) ∧
      (∀ a : A, T.hom a = A.ρ g a) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_monoidHom_subgroupOf_conj_smul_and_hom_res_apply.solution
