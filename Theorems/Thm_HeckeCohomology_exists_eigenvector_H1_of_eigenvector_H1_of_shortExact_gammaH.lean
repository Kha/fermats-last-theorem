import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import P2M.Util
import P2M.Sol.S_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH

set_option autoImplicit false

theorem HeckeCohomology.exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
    (N r : ℕ) [NeZero N] (hrN : r ∣ N) (hr : 4 ≤ r) (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ u ∈ H, ZMod.castHom hrN (ZMod r) (u : ZMod N) = 1)
    {κ : Type} [Field κ]
    {X : CategoryTheory.ShortComplex (Rep κ ↥(CohCarrier.GammaH N H))} (hX : X.ShortExact)
    [Module.Finite κ X.X₂]
    {ι : Type} (S₁ S₂ : ι → Subgroup ↥(CohCarrier.GammaH N H)) (c : ∀ i, ↥(S₂ i) →* ↥(S₁ i))
    [∀ i, (S₂ i).FiniteIndex]
    (φ₂ : ∀ i, X.X₂ →ₗ[κ] X.X₂) (hφ₂ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i))
    (φ₃ : ∀ i, X.X₃ →ₗ[κ] X.X₃) (hφ₃ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i))
    (hg : ∀ (i : ι) (b : X.X₂), X.g.hom (φ₂ i b) = φ₃ i (X.g.hom b))
    (hcomm : ∀ i j : ι,
      Commute (HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i))
        (HeckeCohomology.heckeH1 (S₁ j) (S₂ j) (c j) X.X₂ (φ₂ j) (hφ₂ j)))
    (lam : ι → κ)
    (hocc : ∃ y : groupCohomology.H1 X.X₃, y ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i) y = lam i • y) :
    ∃ x : groupCohomology.H1 X.X₂, x ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i) x = lam i • x := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH.solution
