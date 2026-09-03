import Definitions.Def_GroupCohomology_TransferHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import P2M.Util
namespace P2MW.S_HeckeCohomology_heckeH1_natural

set_option autoImplicit false

namespace TWNatAux

open groupCohomology HeckeCohomology CategoryTheory

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁)
  {A B : Rep k Γ} (f : A ⟶ B)

theorem mapCocycles₁_id_apply (y : cocycles₁ A) (g : Γ) :
    (mapCocycles₁ (MonoidHom.id Γ) f y) g = f.hom (y g) := rfl

variable [S₂.FiniteIndex] (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
  (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
  (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a))

include hcomm in

theorem heckeZ1_natural (y : cocycles₁ A) :
    heckeZ1 S₁ S₂ c B φB hφB (mapCocycles₁ (MonoidHom.id Γ) f y) =
      mapCocycles₁ (MonoidHom.id Γ) f (heckeZ1 S₁ S₂ c A φA hφA y) := by
  apply cocycles₁_ext
  intro γ
  rw [heckeZ1_apply, mapCocycles₁_id_apply, heckeZ1_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mapCocycles₁_id_apply, Rep.hom_comm_apply, hcomm]

end TWNatAux

open groupCohomology HeckeCohomology in
theorem solution {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) {A B : Rep k Γ} [S₂.FiniteIndex] (f : A ⟶ B)
    (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
    (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
    (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a)) (x : H1 A) :
    heckeH1 S₁ S₂ c B φB hφB (map (MonoidHom.id Γ) f 1 x) =
      map (MonoidHom.id Γ) f 1 (heckeH1 S₁ S₂ c A φA hφA x) := by
  induction x using H1_induction_on with
  | h y =>
    rw [H1π_comp_map_apply, heckeH1_H1π S₁ S₂ c B φB hφB, heckeH1_H1π S₁ S₂ c A φA hφA,
      H1π_comp_map_apply, TWNatAux.heckeZ1_natural S₁ S₂ c f φA hφA φB hφB hcomm]
