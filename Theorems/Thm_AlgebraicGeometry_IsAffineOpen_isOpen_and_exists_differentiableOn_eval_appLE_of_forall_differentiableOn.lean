import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Topology

theorem AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn
    (M : Scheme.{0}) (U : M.Opens) (hU : IsAffineOpen U)
    (D : Set ℂ) (hD : IsOpen D)
    (σ : ℂ → (↑(M.presheaf.obj (op U)) →+* ℂ))
    (hσ : ∀ a : ↑(M.presheaf.obj (op U)), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F D ∧ ∀ w ∈ D, σ w a = F w)
    (U' : M.Opens) (s : ↑(M.presheaf.obj (op U'))) :
    IsOpen {w : ℂ | w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'} ∧
    ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G {w : ℂ | w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'} ∧
      ∀ (w : ℂ), w ∈ D → ∀ (hw : ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'),
        G w = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ hw) s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn.solution
