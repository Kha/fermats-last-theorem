import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod

set_option autoImplicit false

theorem
CuspidalType.exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
      (ρW : Representation (ZMod p) (CuspidalType.GL2 q) W)
    (πW : ↥(CuspidalType.steinberg q (ZMod p)).toSubmodule →ₗ[ZMod p] W)
    (hπW : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q (ZMod p)).toSubmodule,
        πW ⟨CuspidalType.ind q (ZMod p) g v, (CuspidalType.steinberg q (ZMod p)).apply_mem_toSubmodule g v.2⟩ =
          ρW g (πW v))
    (hπWsurj : Function.Surjective πW)
    (hπWker : ∀ v : ↥(CuspidalType.steinberg q (ZMod p)).toSubmodule,
        πW v = 0 ↔ ∃ c : ZMod p, (v : CuspidalType.ProjLine q →₀ ZMod p) = c • CuspidalType.constFun q (ZMod p))
    (k : Type) [Field k] [Algebra (ZMod p) k]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q k).toSubmodule →ₗ[k] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q k).toSubmodule,
        π ⟨CuspidalType.ind q k g v, (CuspidalType.steinberg q k).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q k).toSubmodule,
        π v = 0 ↔ ∃ c : k, (v : CuspidalType.ProjLine q →₀ k) = c • CuspidalType.constFun q k)
    :
    ∃ j : W →ₛₗ[algebraMap (ZMod p) k] V,
      (∀ (g : CuspidalType.GL2 q) (w : W), j (ρW g w) = ρ g (j w)) ∧
        ∃ (d : ℕ) (bW : Module.Basis (Fin d) (ZMod p) W) (bV : Module.Basis (Fin d) k V),
          ∀ s : Fin d, bV s = j (bW s) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod.solution
