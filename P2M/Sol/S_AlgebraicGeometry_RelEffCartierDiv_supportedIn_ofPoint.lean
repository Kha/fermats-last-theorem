import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (hU : ∀ t : T, a t ∈ U) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  intro x hx
  have hcl : (closure (Set.range ⇑(graphOver f a ha)) : Set ↥(pullback f g)) = Set.range ⇑(graphOver f a ha) :=
    (graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq
  have hx' : x ∈ Set.range ⇑(graphOver f a ha) := by
    have h2 := hx
    rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker] at h2
    rw [← hcl]
    exact h2
  obtain ⟨t, rfl⟩ := hx'
  change pullback.fst f g (graphOver f a ha t) ∈ U
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact hU t
