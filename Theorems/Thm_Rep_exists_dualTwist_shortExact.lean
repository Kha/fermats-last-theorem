import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_Rep_exists_dualTwist_shortExact

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_dualTwist_shortExact {k G : Type u} [Field k] [Group G] (χ : G →* kˣ)
    {M' M M'' : Rep.{u} k G} (i : M' ⟶ M) (π : M ⟶ M'')
    (hi : Function.Injective i.hom) (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m) :
    ∃ (πD : M''.dualTwist χ ⟶ M.dualTwist χ) (iD : M.dualTwist χ ⟶ M'.dualTwist χ),
      (∀ (f : M''.dualTwist χ) (m : M), (πD.hom f : Module.Dual k M) m = (f : Module.Dual k M'') (π.hom m)) ∧
      (∀ (f : M.dualTwist χ) (m' : M'), (iD.hom f : Module.Dual k M') m' = (f : Module.Dual k M) (i.hom m')) ∧
      Function.Injective πD.hom ∧ Function.Surjective iD.hom ∧
      (∀ f : M.dualTwist χ, iD.hom f = 0 ↔ ∃ f'' : M''.dualTwist χ, πD.hom f'' = f) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_dualTwist_shortExact.solution
