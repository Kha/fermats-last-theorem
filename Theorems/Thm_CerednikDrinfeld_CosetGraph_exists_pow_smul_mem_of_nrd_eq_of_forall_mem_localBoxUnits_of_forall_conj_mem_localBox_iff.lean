import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (wbar : (ℍ[ℚ, a, b])ˣ)
    (hnrd : QuaternionAlgebra.nrd (wbar : ℍ[ℚ, a, b]) = (q : ℚ))
    (hunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        CosetGraph.toLoc w wbar ∈ Submodule.localBoxUnits R w)
    (hnorm : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ x : CosetGraph.Loc a b w,
        ((((CosetGraph.toLoc w wbar)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) * x *
            ((CosetGraph.toLoc w wbar : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox R w ↔
          x ∈ Submodule.localBox R w) ∧
        ((((CosetGraph.toLoc w wbar)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) * x *
            ((CosetGraph.toLoc w wbar : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w ↔
          x ∈ Submodule.localBox Λ w)) :
    ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • ((wbar : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff.solution
