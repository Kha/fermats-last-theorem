import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (W : Y.Opens) (hW : IsAffineOpen W) (hyW : y ∈ W)
    (U : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ q ⁻¹ᵁ W) (hhU : IsAffineOpen (h ⁻¹ᵁ U)) :
    letI : Algebra Γ(Y, W) Γ(X, U) := (q.appLE W U hUW).hom.toAlgebra
    letI : Algebra Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := (q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI : Algebra Γ(Y, W) (Y.residueField y) := (Y.evaluation W y hyW).hom.toAlgebra
    Function.Bijective
      ((AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl) :
          Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U)).toLinearMap.rTensor (Y.residueField y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.solution
