import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_exists_iSup_eq_top_isFrameOn_of_isSectionRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hva : Scheme.Modules.ClosedImmersionBySections L f) :
    ∃ (N : ℕ) (τ : Fin (N + 1) → 𝓡 1) (V : Fin (N + 1) → X.Opens),
      (⨆ i, V i) = ⊤ ∧ ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 (τ i)) (V i) := by
  obtain ⟨N, 𝔓, -⟩ := hva
  have hsurj : ∀ i : Fin (N + 1), ∃ t : 𝓡 1, ι 1 t = (tensorPowOneIso L).symm.hom.app ⊤ (𝔓.σ i) :=
    fun i => (hR.bijective 1).2 _
  choose τ hτ using hsurj
  refine ⟨N, τ, fun i => 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i), ?_, ?_⟩
  · exact 𝔓.toProj.iSup_preimage_eq_top
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
        (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X S N))
  · intro i
    rw [hτ i]
    have hfr : IsFrameOn (𝔓.σ i) (𝔓.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) :=
      fun W hWU hWV => 𝔓.frame i W hWV
    exact hfr.map_iso (tensorPowOneIso L).symm
