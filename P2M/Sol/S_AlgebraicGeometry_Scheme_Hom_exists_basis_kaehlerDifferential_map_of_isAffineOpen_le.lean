import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem solution
    {B : Type u} [CommRing B] {X : Scheme.{u}} (gX : X ⟶ Spec (CommRingCat.of B))
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W) {ι : Type v} :
    letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra W'
    letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, W) Γ(X, W')] (b : Module.Basis ι Γ(X, W) (Ω[Γ(X, W)⁄B])),
      ∃ b' : Module.Basis ι Γ(X, W') (Ω[Γ(X, W')⁄B]),
        ∀ i, b' i = KaehlerDifferential.map B B Γ(X, W) Γ(X, W') (b i) := by
  letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra W'
  letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  intro _inst b

  have hEt : RingHom.Etale (X.presheaf.map (homOfLE hle).op).hom := by
    have h := HasRingHomProperty.appLE (P := @Etale) (Q := @RingHom.Etale) (𝟙 X) inferInstance
      ⟨W, hW⟩ ⟨W', hW'⟩ (by simpa using hle)
    simp [Scheme.Hom.appLE] at h
    exact h
  haveI : Algebra.FormallyEtale Γ(X, W) Γ(X, W') := hEt.formallyEtale
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale B Γ(X, W) Γ(X, W')
  refine ⟨(Algebra.TensorProduct.basis Γ(X, W') b).map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
