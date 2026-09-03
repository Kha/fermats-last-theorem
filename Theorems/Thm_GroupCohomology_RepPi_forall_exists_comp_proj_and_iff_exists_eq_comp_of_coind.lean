import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepPi_forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind

set_option autoImplicit false
open CategoryTheory

theorem GroupCohomology.RepPi.forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind
    {G : Type} [Group G] {ι : Type} [Finite ι] (D : ι → Subgroup G) (Y : ∀ i, Rep ℤ ↥(D i))
    {R P : Rep ℤ G} (f : R ⟶ P)
    (T : ι → Type) [∀ i, AddCommGroup (T i)]
    (Λ : ∀ i, (Rep.res (D i).subtype R ⟶ Y i) →+ T i)
    (hsurj : ∀ i, Function.Surjective (Λ i))
    (hker : ∀ (i) (s : Rep.res (D i).subtype R ⟶ Y i),
      Λ i s = 0 ↔ ∃ χ : Rep.res (D i).subtype P ⟶ Y i, s = (Rep.resFunctor (D i).subtype).map f ≫ χ) :
    (∀ t : ∀ i, T i, ∃ s : R ⟶ GroupCohomology.RepPi.obj (fun i => Rep.coind (D i).subtype (Y i)),
        ∀ i, Λ i (((Rep.resCoindAdjunction ℤ (D i).subtype).homEquiv R (Y i)).symm
          (s ≫ GroupCohomology.RepPi.proj (fun i => Rep.coind (D i).subtype (Y i)) i)) = t i) ∧
    (∀ s : R ⟶ GroupCohomology.RepPi.obj (fun i => Rep.coind (D i).subtype (Y i)),
        (∀ i, Λ i (((Rep.resCoindAdjunction ℤ (D i).subtype).homEquiv R (Y i)).symm
          (s ≫ GroupCohomology.RepPi.proj (fun i => Rep.coind (D i).subtype (Y i)) i)) = 0) ↔
        ∃ χ : P ⟶ GroupCohomology.RepPi.obj (fun i => Rep.coind (D i).subtype (Y i)), s = f ≫ χ) := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepPi_forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind.solution
