import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ = Y.fromSpecStalk (genericPoint Y))
      (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O)
      (_ : ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0)
      (φ : CommRingCat.of O ⟶ X.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one.solution
