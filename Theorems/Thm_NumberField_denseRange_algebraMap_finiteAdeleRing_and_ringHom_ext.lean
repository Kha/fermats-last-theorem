import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext
set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext
    (K : Type) [Field K] [NumberField K] :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) ∧
    (∀ (R : Type) [Ring R] [TopologicalSpace R] [T2Space R]
        (Ψ Ψ' : FiniteAdeleRing (𝓞 K) K →+* R), Continuous Ψ → Continuous Ψ' →
        (∀ a : K, Ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) = Ψ' (algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) → Ψ = Ψ') := by p2m_exact_reverting @_root_.P2MW.S_NumberField_denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext.solution
