import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_disjoint_of_finite_of_isClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} (S : Set X) (hS : S.Finite) (hcl : ∀ s ∈ S, IsClosed ({s} : Set X))
    (x : X) (hx : x ∉ S) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Disjoint (V : Set X) S := by
  classical
  have hSc : IsClosed S := by
    have h : S = ⋃ s ∈ S, ({s} : Set X) := (Set.biUnion_of_singleton S).symm
    rw [h]
    exact hS.isClosed_biUnion fun s hs => hcl s hs
  let U : X.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hxU : x ∈ U := hx
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
  exact ⟨V, hV, hxV, Set.disjoint_left.mpr fun z hz hzS => (hVU hz) hzS⟩
