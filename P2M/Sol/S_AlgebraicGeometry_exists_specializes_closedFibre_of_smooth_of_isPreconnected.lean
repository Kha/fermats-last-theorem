import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_specializes_closedFibre_of_smooth_of_isPreconnected
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [QuasiCompact g]
    (hne : ∃ x : G, g.base x = IsLocalRing.closedPoint R)
    (hconn : _root_.IsPreconnected {x : G | g.base x = IsLocalRing.closedPoint R}) :
    ∃ η : G, g.base η = IsLocalRing.closedPoint R ∧
      (∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x) ∧
      (∀ y : G, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) := by

  set s : ↥(Spec (CommRingCat.of R)) := IsLocalRing.closedPoint R with hs
  let Φ : Scheme.{u} := g.fiber s
  let φ : Φ ⟶ Spec ((Spec (CommRingCat.of R)).residueField s) := g.fiberToSpecResidueField s
  haveI : Smooth φ := by
    show Smooth (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
    infer_instance

  let e : ↥Φ ≃ₜ ↥(g.base ⁻¹' {s}) := g.fiberHomeo s
  have hrange : Set.range (g.fiberι s).base = g.base ⁻¹' {s} := g.range_fiberι s
  haveI : Nonempty ↥Φ := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e.symm ⟨x, hx⟩⟩
  haveI : PreconnectedSpace ↥Φ := by
    have h1 : PreconnectedSpace ↥(g.base ⁻¹' {s}) := isPreconnected_iff_preconnectedSpace.mp hconn
    constructor
    rw [← Set.image_univ_of_surjective e.symm.surjective]
    exact isPreconnected_univ.image _ e.symm.continuous.continuousOn

  haveI : IsIntegral Φ :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (k := ↥((Spec (CommRingCat.of R)).residueField s)) φ

  let η₀ : ↥Φ := genericPoint ↥Φ
  have hη₀ : ∀ z : ↥Φ, η₀ ⤳ z := fun z => (genericPoint_spec ↥Φ).specializes (Set.mem_univ z)
  refine ⟨(g.fiberι s).base η₀, ?_, ?_, ?_⟩
  · have : (g.fiberι s).base η₀ ∈ g.base ⁻¹' {s} := hrange ▸ Set.mem_range_self _
    exact this
  · intro x hx
    obtain ⟨x', rfl⟩ : x ∈ Set.range (g.fiberι s).base := by rw [hrange]; exact hx
    exact (hη₀ x').map (g.fiberι s).continuous
  · intro y hy hys
    obtain ⟨y', rfl⟩ : y ∈ Set.range (g.fiberι s).base := by rw [hrange]; exact hys
    exact ((hη₀ y').map (g.fiberι s).continuous).antisymm hy |>.eq.symm
