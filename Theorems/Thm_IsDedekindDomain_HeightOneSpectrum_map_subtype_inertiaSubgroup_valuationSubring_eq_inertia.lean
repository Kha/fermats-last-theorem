import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.PlaceDecomp

theorem IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    (((w.valuation F).valuationSubring).inertiaSubgroup E).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype =
      w.asIdeal.inertia (F ≃ₐ[E] F) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia.solution
