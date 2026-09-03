import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_finite_of_isOrder

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N m : ℕ} (hm : 0 < m)
    {B : Type} [CommRing B] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) : Finite G := by
  classical
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg

  let Nm : Submodule ℤ ↥Λ := LinearMap.range (DistribMulAction.toLinearMap ℤ ↥Λ m)
  have hNm : ∀ x : ↥Λ, x ∈ Nm ↔ ∃ y : ↥Λ, m • y = x := fun x => LinearMap.mem_range
  haveI : Module.Finite ℤ (↥Λ ⧸ Nm) := Module.Finite.quotient ℤ Nm
  have htors : Module.IsTorsion ℤ (↥Λ ⧸ Nm) := by
    intro q
    refine ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm.ne')⟩, ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Nm q
    change Submodule.Quotient.mk (p := Nm) ((m : ℤ) • x) = 0
    rw [Submodule.Quotient.mk_eq_zero, hNm]
    exact ⟨x, (natCast_zsmul x m).symm⟩
  haveI : Finite (↥Λ ⧸ Nm) := Module.finite_of_fg_torsion _ htors

  refine Finite.of_injective (fun g => Submodule.Quotient.mk (p := Nm) (χ g)) ?_
  intro g g' hgg'
  have hmem : χ g - χ g' ∈ Nm := (Submodule.Quotient.eq Nm).mp hgg'
  obtain ⟨y, hy⟩ := (hNm _).mp hmem
  apply hρ.label_injective g g'
  refine ⟨y, ?_⟩
  have := congrArg (fun z : ↥Λ => (z : ℍ[ℚ, a, b])) hy
  simp only [Submodule.coe_sub] at this
  rw [← this, Nat.cast_smul_eq_nsmul]
  exact Submodule.coe_smul_of_tower m y
