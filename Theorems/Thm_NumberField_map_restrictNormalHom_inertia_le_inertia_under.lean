import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_map_restrictNormalHom_inertia_le_inertia_under
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem NumberField.map_restrictNormalHom_inertia_le_inertia_under
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) :
    (w.asIdeal.inertia (F ≃ₐ[E] F)).map (AlgEquiv.restrictNormalHom L)
      ≤ (w.under (𝓞 L)).asIdeal.inertia (L ≃ₐ[E] L) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_map_restrictNormalHom_inertia_le_inertia_under.solution
