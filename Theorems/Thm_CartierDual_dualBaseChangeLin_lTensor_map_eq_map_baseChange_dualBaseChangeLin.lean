import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin
    (O : Type) [CommRing O] (F : Type) [CommRing F] [Algebra O F]
    (A : Type) [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Free O A]
    (f : A →ₐc[O] A) (w : F ⊗[O] CartierDual O A) :
    CartierDual.dualBaseChangeLin O F A
        (LinearMap.lTensor F ((CartierDual.map f : CartierDual O A →ₐc[O] CartierDual O A) :
          CartierDual O A →ₗ[O] CartierDual O A) w) =
      CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id F F) f)
        (CartierDual.dualBaseChangeLin O F A w) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin.solution
