import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
    (k : Type) [Field k] [IsAlgClosed k]
    {L L' : Type} [Field L] [Field L'] [Algebra k L] [Algebra k L']
    (M : CurveModel k L) (M' : CurveModel k L')
    (d : M'.C ⟶ M.C) (hd : d ≫ M.toBase = M'.toBase) [IsFinite d] (hsurj : Function.Surjective d.base) :
    ∃ (φ : L →ₐ[k] L') (hfin : FiniteAlong k φ) (hint : φ.toRingHom.IsIntegral),
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (d ⁻¹ᵁ U))]
        (t : Γ(M.C, U)),
        φ (M.ffEquiv.symm (M.C.germToFunctionField U t)) =
          M'.ffEquiv.symm (M'.C.germToFunctionField (d ⁻¹ᵁ U) ((d.app U).hom t))) ∧
      ∀ R : Place k L',
        (M.pointEquivPlace.symm (R.restrictAlong φ hint)).1 = (M'.pointEquivPlace.symm R).1 ≫ d := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.solution
