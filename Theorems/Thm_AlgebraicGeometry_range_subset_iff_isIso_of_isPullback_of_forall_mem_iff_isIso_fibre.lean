import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
    {𝒳 Y 𝒵 : Scheme.{u}} (p : 𝒵 ⟶ Y) (q : 𝒳 ⟶ Y) (h : 𝒵 ⟶ 𝒳) (w : h ≫ q = p)
    (U : Y.Opens)
    (hU : ∀ y : Y, y ∈ (U : Set Y) ↔
      IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (hUiso : IsIso (pullback.map p U.ι q U.ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w])
      (by rw [Category.comp_id, Category.id_comp])))
    {T Z X' : Scheme.{u}} (t : T ⟶ Y)
    (pZ : Z ⟶ T) (eZ : Z ⟶ 𝒵) (hZ : IsPullback eZ pZ p t)
    (qX : X' ⟶ T) (eX : X' ⟶ 𝒳) (hX : IsPullback eX qX q t)
    (φ : Z ⟶ X') (hφ₁ : φ ≫ qX = pZ) (hφ₂ : φ ≫ eX = eZ ≫ h) :
    Set.range t.base ⊆ (U : Set Y) ↔ IsIso φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre.solution
