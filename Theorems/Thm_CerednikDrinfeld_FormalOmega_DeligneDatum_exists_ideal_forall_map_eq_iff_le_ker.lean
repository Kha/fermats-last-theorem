import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_ideal_forall_map_eq_iff_le_ker

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped TensorProduct

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_ideal_forall_map_eq_iff_le_ker
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d₁ d₂ : DeligneDatum (K := K) π B) :
    ∃ I : Ideal B, ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C),
      d₁.map π χ = d₂.map π χ ↔ I ≤ RingHom.ker (χ : B →+* C) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_ideal_forall_map_eq_iff_le_ker.solution
