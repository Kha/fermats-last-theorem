import Definitions.Def_GroupCohomology_TransferHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import P2M.Util
import P2M.Sol.S_HeckeCohomology_heckeH1_natural

set_option autoImplicit false
open groupCohomology in

theorem HeckeCohomology.heckeH1_natural {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) {A B : Rep k Γ} [S₂.FiniteIndex] (f : A ⟶ B)
    (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
    (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
    (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a)) (x : H1 A) :
    heckeH1 S₁ S₂ c B φB hφB (map (MonoidHom.id Γ) f 1 x) =
      map (MonoidHom.id Γ) f 1 (heckeH1 S₁ S₂ c A φA hφA x) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_heckeH1_natural.solution
