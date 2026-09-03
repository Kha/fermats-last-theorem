import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Ws23C2cD

open TopologicalSpace

theorem main {X Y : Scheme.{u}} (p : X ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (y : Y) (hy : y ∈ U)
    (s : Γ(X, p ⁻¹ᵁ U)) (hs : ∀ x : X, p.base x = y → x ∈ X.basicOpen s) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧ p ⁻¹ᵁ V.1 ≤ X.basicOpen s := by
  have hFc : IsClosed ((X.basicOpen s : Set X)ᶜ) := (X.basicOpen s).2.isClosed_compl
  have hIm : IsClosed (p.base '' ((X.basicOpen s : Set X)ᶜ)) := p.isClosedMap _ hFc
  have hyn : y ∉ p.base '' ((X.basicOpen s : Set X)ᶜ) := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hs x hxy)
  let W : Y.Opens := U ⊓ ⟨(p.base '' ((X.basicOpen s : Set X)ᶜ))ᶜ, hIm.isOpen_compl⟩
  have hyW : y ∈ (W : Set Y) := ⟨hy, hyn⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyW W.2
  refine ⟨⟨V, hV⟩, hyV, fun v hv => (hVW hv).1, fun x hx => ?_⟩
  by_contra hxs
  exact (hVW hx).2 ⟨x, hxs, rfl⟩

end Ws23C2cD

theorem solution
    {X Y : Scheme.{u}} (p : X ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (y : Y) (hy : y ∈ U)
    (s : Γ(X, p ⁻¹ᵁ U)) (hs : ∀ x : X, p.base x = y → x ∈ X.basicOpen s) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧ p ⁻¹ᵁ V.1 ≤ X.basicOpen s :=
  Ws23C2cD.main p U y hy s hs
