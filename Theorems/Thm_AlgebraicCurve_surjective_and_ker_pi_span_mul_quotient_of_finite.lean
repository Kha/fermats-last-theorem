import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_surjective_and_ker_pi_span_mul_quotient_of_finite

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C))
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U)
    (B : Subalgebra Γ(C, U) C.functionField) (hB : Module.Finite Γ(C, U) B) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

    let Bz : C → Submodule k C.functionField := fun z =>
      Submodule.span k ((B : Set C.functionField) * Set.range (algebraMap (C.presheaf.stalk z) C.functionField))
    let Q : C → Type u := fun z =>
      ↥(Bz z) ⧸ (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))).comap (Bz z).subtype

    let φ : ↥(Submodule.span k (B : Set C.functionField)) →ₗ[k]
        ((z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (Submodule.span_mono
        (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)))
    Function.Surjective φ ∧
      LinearMap.ker φ = (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom)).comap
        (Submodule.span k (B : Set C.functionField)).subtype ∧
      {z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}, FiniteDimensional k (Q z.1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_surjective_and_ker_pi_span_mul_quotient_of_finite.solution
