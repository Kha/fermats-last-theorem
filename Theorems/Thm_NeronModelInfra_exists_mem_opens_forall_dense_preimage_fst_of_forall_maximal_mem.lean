import Mathlib
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : (pullback f f).Opens)
    (hZ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z)
    (ξ : X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ) :
    ∃ N : X.Opens, ξ ∈ N ∧ ∀ a : X, a ∈ N → f.base a = IsLocalRing.closedPoint R →
      Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = a} → ↑(pullback f f)) ⁻¹'
        (Z : Set ↑(pullback f f))) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem.solution
