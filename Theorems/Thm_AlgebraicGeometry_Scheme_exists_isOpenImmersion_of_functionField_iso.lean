import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_of_functionField_iso
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsIntegral C'] [LocallyOfFiniteType c] [LocallyOfFiniteType c']
    (ψ : C.functionField ≅ C'.functionField)
    (hψ : Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') ≫ c' =
      C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ (U : C.Opens) (hη : genericPoint C ∈ U) (j : (U : Scheme.{u}) ⟶ C') (_ : IsOpenImmersion j),
      j ≫ c' = U.ι ≫ c ∧
      U.fromSpecStalkOfMem (genericPoint C) hη ≫ j =
        Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso.solution
