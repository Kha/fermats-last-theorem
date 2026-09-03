import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_orderedAffineCover_orderEmbedding_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_orderedAffineCover_orderEmbedding_of_sup_eq_top
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover) :
    ∃ (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι),
      (∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) ∧ (∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a) ∧
      (∀ b a, eV b < eU a) ∧ ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_orderedAffineCover_orderEmbedding_of_sup_eq_top.solution
