import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion MatrixGroups

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (q : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule q B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁)
    (c₀ : ℕ) (e : ↥R₁ → (A₀.A ⟶ A₀.A)) (he : ∀ x : ↥R₁, e x ≫ A₀.f = A₀.f)
    (hhom : ∀ (x : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (e x) (he x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e x) (he x) Q))
    (hlin : ∀ (x : ↥R₁) (m : ↥Λ), A₀.act m ≫ e x = e x ≫ A₀.act m)
    (hadd : ∀ (x y : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e (x + y)) (he (x + y)) P = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e y) (he y) P))
    (hmul : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₁)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      nsmulPt A₀.L t (q ^ c₀) (pushPt (e ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩) (he _) P) =
        pushPt (e x) (he x) (pushPt (e y) (he y) P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e ⟨1, hR₁.one_mem⟩) (he _) P = nsmulPt A₀.L t (q ^ c₀) P)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (𝓔 : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∃ g : GL (Fin 2) K₀, ∀ (x : ↥R₁) (u : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
      IsFormalCompletionAlong θ₀ θ₀ (e x) (he x) (MvFormalGroup.Hom.toPowerSeries (u : MvFormalGroup.End X₀.F)) →
        𝓔 u = ((q : K₀) ^ c₀) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
          ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong.solution
