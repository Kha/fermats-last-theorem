import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~finite_and_natCard_sections_le_of_finrank_specialFibre_le"

theorem AlgebraicGeometry.finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (V : Y.Opens) (B : ℕ)
    (hB : letI := Scheme.TwoAffineOpenCover.algebraOfHom q V
      Module.Finite (IsLocalRing.ResidueField R) Γ(Y, V) ∧
        Module.finrank (IsLocalRing.ResidueField R) Γ(Y, V) ≤ B) :
    Finite {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} ∧
      Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧
        s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} ≤ B := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le.solution
