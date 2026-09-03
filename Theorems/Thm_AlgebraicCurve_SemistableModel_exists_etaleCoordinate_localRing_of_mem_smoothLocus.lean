import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.exists_etaleCoordinate_localRing_of_mem_smoothLocus
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∃ (ι : ↥A →+* ↥S) (_ : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
      (t : ↥S) (χ₀ : ↥S →+* ResidueField ↥A),
      IsLocalRing ↥S ∧
      (∀ f : ↥S, IsUnit f ↔ χ₀ f ≠ 0) ∧
      (∀ a : ↥A, χ₀ (ι a) = IsLocalRing.residue ↥A a) ∧
      χ₀ t = 0 ∧
      (Polynomial.eval₂RingHom ι t).FormallySmooth ∧ (Polynomial.eval₂RingHom ι t).FormallyUnramified ∧
      (∀ f : ↥S, χ₀ f = 0 → ∃ g : ↥S, ∃ s ∈ (maximalIdeal ↥A).map ι, f = g * t + s) ∧
      ((maximalIdeal ↥A).map ι).IsPrime ∧ t ∉ (maximalIdeal ↥A).map ι ∧
      IsNoetherianRing (↥S ⧸ (maximalIdeal ↥A).map ι) ∧
      (∀ f : F, f ∈ SemistableModel.localRing X φ η ↔
        ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∃ (P : Type) (_ : CommRing P) (_ : Algebra ↥A P) (_ : Algebra.FinitePresentation ↥A P)
          (M : Submonoid P) (_ : Algebra P ↥S) (_ : IsLocalization M ↥S),
        ∀ a : ↥A, algebraMap P ↥S (algebraMap ↥A P a) = ι a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus.solution
