import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing AlgebraicGeometry.Polarisation AlgebraicGeometry.SmallExtension
open scoped Quaternion TensorProduct

theorem CerednikDrinfeld.QM.FakeEllipticCurve.unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hsmall : ∀ x ∈ RingHom.ker (algebraMap B₁ B₀), ∀ m ∈ maximalIdeal B₁, x * m = 0)
    (hI : RingHom.ker (algebraMap B₁ B₀) ≤ maximalIdeal B₁)
    (V : Type) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker (algebraMap B₁ B₀)))

    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A) [IsAffineHom g]
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (Ek : FakeEllipticCurve Λ N (ResidueField B₁)) (ik : Ek.A ⟶ E.A) [IsAffineHom ik]
    (hik : FakeEllipticCurve.IsPullbackVia (residue B₁) E Ek ik)

    (gXX : pullback E₀.f E₀.f ⟶ pullback E.f E.f) [IsAffineHom gXX]
    (hg₁ : gXX ≫ pullback.fst E.f E.f = pullback.fst E₀.f E₀.f ≫ g)
    (hg₂ : gXX ≫ pullback.snd E.f E.f = pullback.snd E₀.f E₀.f ≫ g)
    (iXX : pullback Ek.f Ek.f ⟶ pullback E.f E.f) [IsAffineHom iXX]
    (hi₁ : iXX ≫ pullback.fst E.f E.f = pullback.fst Ek.f Ek.f ≫ ik)
    (hi₂ : iXX ≫ pullback.snd E.f E.f = pullback.snd Ek.f Ek.f ≫ ik)

    (𝓛₀ : E₀.A.Modules) (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star)
    (𝒲 : (pullback E.f E.f).OrderedAffineCover)
    (C : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁]
      (OModulePresheaf.unit (pullback.fst Ek.f Ek.f ≫ Ek.f)).cochain (𝒲.comap iXX) 2)
    (hC : IsPicObstructionCocycle V ι (pullback.fst E.f E.f ≫ E.f) (pullback.fst Ek.f Ek.f ≫ Ek.f) iXX gXX 𝒲
      (mumfordBundle E₀.f E₀.L 𝓛₀) C)
    (x : ↥Λ)

    (𝒲' : (pullback E.f E.f).OrderedAffineCover) (lamA lamB : 𝒲'.ι → 𝒲.ι)
    (hA : ∀ w, 𝒲'.U w ≤
      (pullback.lift (pullback.fst E.f E.f) (pullback.snd E.f E.f ≫ E.act x)
        (by rw [Category.assoc, E.act_over]; exact pullback.condition)) ⁻¹ᵁ 𝒲.U (lamA w))
    (hB : ∀ w, 𝒲'.U w ≤
      (pullback.lift (pullback.fst E.f E.f ≫ E.act (star x)) (pullback.snd E.f E.f)
        (by rw [Category.assoc, E.act_over]; exact pullback.condition)) ⁻¹ᵁ 𝒲.U (lamB w))
    (hkA : ∀ w, (𝒲'.comap iXX).U w ≤
      (pullback.lift (pullback.fst Ek.f Ek.f) (pullback.snd Ek.f Ek.f ≫ Ek.act x)
        (by rw [Category.assoc, Ek.act_over]; exact pullback.condition)) ⁻¹ᵁ (𝒲.comap iXX).U (lamA w))
    (hkB : ∀ w, (𝒲'.comap iXX).U w ≤
      (pullback.lift (pullback.fst Ek.f Ek.f ≫ Ek.act (star x)) (pullback.snd Ek.f Ek.f)
        (by rw [Category.assoc, Ek.act_over]; exact pullback.condition)) ⁻¹ᵁ (𝒲.comap iXX).U (lamB w)) :
    ∀ ξ : Module.Dual (ResidueField B₁) V,
      OModulePresheaf.unitPullback (πX := pullback.fst Ek.f Ek.f ≫ Ek.f)
          (pullback.lift (pullback.fst Ek.f Ek.f) (pullback.snd Ek.f Ek.f ≫ Ek.act x)
            (by rw [Category.assoc, Ek.act_over]; exact pullback.condition))
          (𝒲'.comap iXX) (𝒲.comap iXX) lamA hkA 2 (C ξ) -
        OModulePresheaf.unitPullback (πX := pullback.fst Ek.f Ek.f ≫ Ek.f)
          (pullback.lift (pullback.fst Ek.f Ek.f ≫ Ek.act (star x)) (pullback.snd Ek.f Ek.f)
            (by rw [Category.assoc, Ek.act_over]; exact pullback.condition))
          (𝒲'.comap iXX) (𝒲.comap iXX) lamB hkB 2 (C ξ) ∈
      LinearMap.range ((OModulePresheaf.unit (pullback.fst Ek.f Ek.f ≫ Ek.f)).d (𝒲'.comap iXX) 1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle.solution
