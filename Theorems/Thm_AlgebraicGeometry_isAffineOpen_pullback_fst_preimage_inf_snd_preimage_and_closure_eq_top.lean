import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
    {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
    Subring.closure
      (Set.range (fun s : Γ(X, U) =>
          (pullback f g).presheaf.map
            (homOfLE (inf_le_left : pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ U)).op
            ((pullback.fst f g).app U s)) ∪
        Set.range (fun t : Γ(Y, V) =>
          (pullback f g).presheaf.map
            (homOfLE (inf_le_right : pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.snd f g ⁻¹ᵁ V)).op
            ((pullback.snd f g).app V t))) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top.solution
