import Mathlib
import P2M.Util
import P2M.Sol.S_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero

universe u v

theorem Deformation.exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (M : Type v) [AddCommGroup M] (n : ℕ) (hM : ∀ x : M, (p ^ n : ℤ) • x = 0) :
    ∃ inst : Module 𝓞 M,
      (∀ (m : ℤ) (x : M), @HSMul.hSMul 𝓞 M M (@instHSMul 𝓞 M inst.toSMul) (m : 𝓞) x = m • x) ∧
      (∀ a : 𝓞, ∃ m : ℤ, ∀ x : M, @HSMul.hSMul 𝓞 M M (@instHSMul 𝓞 M inst.toSMul) a x = m • x) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero.solution
