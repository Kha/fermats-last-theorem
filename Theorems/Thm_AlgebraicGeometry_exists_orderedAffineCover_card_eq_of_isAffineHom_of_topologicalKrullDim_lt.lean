import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt
    {k : Type u} [Field k] [Infinite k] {N : ℕ} {X : Scheme.{u}} [NoetherianSpace X]
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) [IsAffineHom φ]
    {n : ℕ} (hdim : topologicalKrullDim X < n) :
    ∃ 𝒦 : X.OrderedAffineCover, Fintype.card 𝒦.ι = n ∧
      ∀ i : 𝒦.ι, ∃ ℓ : MvPolynomial (Fin (N + 1)) k,
        ℓ ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1 ∧
        𝒦.U i = φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) ℓ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_orderedAffineCover_card_eq_of_isAffineHom_of_topologicalKrullDim_lt.solution
