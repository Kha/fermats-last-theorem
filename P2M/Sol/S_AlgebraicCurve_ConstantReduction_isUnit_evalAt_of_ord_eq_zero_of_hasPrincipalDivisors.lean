import Definitions.Def_ModularCurve_FinitePlaceLift
import Theorems.Thm_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors
import P2M.Util
namespace P2MW.S_AlgebraicCurve_ConstantReduction_isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {P : Place K F} (hP : P.IsRational) {f : F} (hf : f ∈ R.integers) (hres : R.residue ⟨f, hf⟩ ≠ 0)
    (hord : (R.placeMap P).ord (R.residue ⟨f, hf⟩) = 0)
    (hfib : ∀ w : Place K F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring) :
    ∃ h : P.evalAt f ∈ A, IsUnit (⟨P.evalAt f, h⟩ : A) := by
  obtain ⟨hm, h, hcomp⟩ :=
    AlgebraicCurve.ConstantReduction.isPointwise_of_hasPrincipalDivisors R P hP f hf hfib
  refine ⟨h, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    ((R.placeMap P).toValuationSubring)
  obtain ⟨u, hu⟩ := (R.placeMap P).exists_unit_mul_zpow hres hπ
  rw [hord, zpow_zero, mul_one] at hu
  have hmem_eq : (⟨R.residue ⟨f, hf⟩, hm⟩ : ((R.placeMap P).toValuationSubring)) = (u : _) :=
    Subtype.ext hu
  have hrhs : IsLocalRing.residue (R.placeMap P).toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩ ≠ 0 := by
    rw [hmem_eq]
    exact ((IsLocalRing.residue _).isUnit_map u.isUnit).ne_zero
  have hlhs : IsLocalRing.residue A ⟨P.evalAt f, h⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcomp
    exact hrhs hcomp.symm
  by_contra hnu
  apply hlhs
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
