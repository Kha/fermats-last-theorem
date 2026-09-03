import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf X' Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [IsFinite (i ≫ g)] (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    letI : Algebra R Γ(Xf, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra
    Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
    Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) =
      Module.finrank (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField R) Γ(Xf, ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite.solution
