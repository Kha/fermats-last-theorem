import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_CartierDual_dualBaseChangeLin_bijective

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.dualBaseChangeLin_bijective.{u, v, w}
    (O : Type u) [CommRing O] (F : Type v) [Field F] [Algebra O F]
    (A : Type w) [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A] [Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O F A) ∧
    CartierDual.dualBaseChangeLin O F A 1 = 1 ∧
    (∀ x y : F ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O F A (x * y)
          = CartierDual.dualBaseChangeLin O F A x * CartierDual.dualBaseChangeLin O F A y) ∧
    (∀ g : CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O F A) (CartierDual.dualBaseChangeLin O F A)
            (tensorToGenericFibre O F (Coalgebra.comul (R := O) g))
          = Coalgebra.comul (R := F) (CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] g))) ∧
    (∀ (g : CartierDual O A) (x : F ⊗[O] A),
        CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := F) x)) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_dualBaseChangeLin_bijective.solution
