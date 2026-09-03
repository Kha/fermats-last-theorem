import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (S : Subring F) [IsLocalRing ↥S] [IsNoetherianRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)

    {ι : Type*} (cst : ι → ↥A)
    (hκ : Function.Surjective (fun i => IsLocalRing.residue ↥A (cst i)))
    (hAS : ∀ i : ι, algebraMap L F (cst i : L) ∈ S)
    (χ : ↥S →+* ResidueField A)
    (hker : RingHom.ker χ = maximalIdeal ↥S)
    (hχA : ∀ i : ι, χ ⟨algebraMap L F (cst i : L), hAS i⟩ = IsLocalRing.residue ↥A (cst i))

    (ϖS t : ↥S)
    (hmax : maximalIdeal ↥S = Ideal.span {ϖS, t})
    (hϖR : (⟨(ϖS : F), hSR ϖS⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers)
    (ht : t ∉ Ideal.span {ϖS})
    (hdom : IsDomain (↥S ⧸ Ideal.span {ϖS}))

    (hng : ∃ f : ↥S, f ∈ maximalIdeal ↥S ∧ R.residue ⟨(f : F), hSR f⟩ ≠ 0)

    (hfracbar : ∀ g : Fbar, ∃ a b : ↥S, R.residue ⟨(b : F), hSR b⟩ ≠ 0 ∧
      g * R.residue ⟨(b : F), hSR b⟩ = R.residue ⟨(a : F), hSR a⟩)

    (Q : Place (ResidueField A) Fbar)
    (hreads : ∀ f : ↥S, R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring ∧
      (R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring.nonunits ↔ f ∈ maximalIdeal ↥S)) :

    (∀ f : ↥S, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ ϖS ∣ f) ∧

    (∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧

    Q.ord (R.residue ⟨(t : F), hSR t⟩) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants.solution
