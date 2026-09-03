import Mathlib
import Definitions.Def_AlgebraicGeometry_BiCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedOpenFamily_exists_orderedAffineCover_inter_image_eq_inf

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.OrderedOpenFamily.exists_orderedAffineCover_inter_image_eq_inf
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j)) (hcov : ⨆ j, 𝔅.U j = ⊤) (p : ℕ) :
    ∃ (𝔚 : ∀ s : 𝔄.Idx p, ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover)
      (e : ∀ s : 𝔄.Idx p, 𝔅.ι ≃o (𝔚 s).ι),
      ∀ (s : 𝔄.Idx p) (j : 𝔅.ι), (𝔄.inter s).ι ''ᵁ (𝔚 s).U (e s j) = 𝔄.inter s ⊓ 𝔅.U j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedOpenFamily_exists_orderedAffineCover_inter_image_eq_inf.solution
