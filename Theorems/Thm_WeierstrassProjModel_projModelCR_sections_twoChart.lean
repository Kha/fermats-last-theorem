import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_projModelCR_sections_twoChart
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.projModelCR_sections_twoChart
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    let 𝒜 := projModelGradingCR V
    let Y : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 1)
    let Z : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 2)
    let hY : Y ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1))
    let hZ : Z ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
    let ρY : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 Y) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 Y hY one_pos).inv
    let ρZ : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 Z) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 Z hZ one_pos).inv
    (∀ s t : Γ(Proj 𝒜, ⊤), ρY s = ρY t → ρZ s = ρZ t → s = t) ∧
    (∀ (a : Away 𝒜 Y) (b : Away 𝒜 Z),
      awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) a = awayMap 𝒜 hY (mul_comm Y Z) b →
      ∃ s : Γ(Proj 𝒜, ⊤), ρY s = a ∧ ρZ s = b) ∧
    (∀ s : Γ(Proj 𝒜, ⊤), awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) (ρY s) = awayMap 𝒜 hY (mul_comm Y Z) (ρZ s)) ∧
    (∀ r : 𝒜 0,
      ρY ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers Y) r ∧
      ρZ ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers Z) r) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projModelCR_sections_twoChart.solution
