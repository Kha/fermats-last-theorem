import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (𝒪 : ValuationSubring F) (resd : ↥𝒪 →+* Fbar) (hsurj : Function.Surjective resd)
    (hker : RingHom.ker resd = maximalIdeal ↥𝒪)
    (hcompat : ∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ 𝒪),
      resd ⟨algebraMap L F (a : L), h⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a))
    (h𝒪 : 𝒪.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    (∀ f : ↥S, (f : F) ∈ 𝒪) ∧
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ 𝒪), f ∈ S ∧ resd ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ 𝒪),
        IsUnit f ↔ Q.ord (resd ⟨(f : F), hR⟩) = 0 ∧ resd ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ 𝒪), Q.ord (resd ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring.solution
