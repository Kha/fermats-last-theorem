import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_levelwise_equiv_transpose_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ, (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q ≃ₗ[R]
        (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).C p q,
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e (p + 1) q ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dH p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dH p q (e p q x)) ∧
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e p (q + 1) ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dV p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dV p q (e p q x)) ∧
      ∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q) (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
        (e p q x : OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 q p) (σ, τ) =
          (X.presheaf.map (homOfLE (le_inf
              (inf_le_right.trans (Scheme.Hom.id_preimage (𝔓.inter σ)).le)
              ((Scheme.Hom.id_preimage (𝒲.inter τ)).ge.trans' inf_le_left) :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ OModulePresheaf.Leray.biOpen (𝟙 X) 𝒲 𝔓 p q τ σ)).op).hom
            (x (τ, σ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id.solution
