import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (B : ℕ)
    (hB : letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
      Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
        Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) ≤ B) :
    Finite {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} ∧ Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} ≤ B := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le.solution
