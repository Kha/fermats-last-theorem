import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    {X Y XK : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] [Flat g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (qK : XK ⟶ Spec (.of K)) (πK : XK ⟶ X)
    (hXK : IsPullback πK qK g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsReduced XK] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
    Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} = Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced.solution
