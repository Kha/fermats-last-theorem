import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_mem_primeHeckeSet_of_nrd_eq_of_forall_finiteAdeleEvalAt_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.mem_primeHeckeSet_of_nrd_eq_of_forall_finiteAdeleEvalAt_eq
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    (O : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ} (hO : QuaternionAlgebra.IsEichlerOrder O M) (hpM : ¬ p ∣ M)
    (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (w : (ℍ[ℚ, a, b])ˣ) (hnrd : QuaternionAlgebra.nrd (w : ℍ[ℚ, a, b]) = (p : ℚ))
    (hunit : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ((p : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      CerednikDrinfeld.CosetGraph.toLoc u w ∈ Submodule.localBoxUnits O u)
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ht : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (t : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (w : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (htv : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (t : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    t ∈ QuaternionAlgebra.primeHeckeSet O p := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_mem_primeHeckeSet_of_nrd_eq_of_forall_finiteAdeleEvalAt_eq.solution
