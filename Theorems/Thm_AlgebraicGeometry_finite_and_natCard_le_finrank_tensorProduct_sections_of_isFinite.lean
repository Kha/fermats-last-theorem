import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf : Scheme.{u}} (g : X ⟶ Spec (.of R)) (i : Xf ⟶ X) [IsFinite (i ≫ g)]
    (Ω : Type u) [Field Ω] [Algebra R Ω] :
    Finite {x : Spec (.of Ω) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R Ω))} ∧
    (letI : Algebra R Γ(Xf, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra
     Module.Finite R Γ(Xf, ⊤) ∧
     Nat.card {x : Spec (.of Ω) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R Ω))} ≤
       Module.finrank (IsLocalRing.ResidueField R)
         (TensorProduct R (IsLocalRing.ResidueField R) Γ(Xf, ⊤))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite.solution
