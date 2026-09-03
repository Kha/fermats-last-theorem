import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import P2M.Util
import P2M.Sol.S_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString

set_option autoImplicit false

theorem Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString
    (D : ℕ) (hD : D ≠ 0)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : ℕ → V)
    (hli : LinearIndependent ℂ (fun d : Nat.divisors D => e (d : ℕ)))
    (hspan : Submodule.span ℂ (Set.range fun d : Nat.divisors D => e (d : ℕ)) = ⊤)
    (U : ℕ → Module.End ℂ V)
    (hcomm : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ D → q ∣ D → Commute (U p) (U q))
    (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q))
    (hbase : ∀ q : ℕ, q.Prime → q ∣ D → ∃ a b : ℂ, ∀ d : ℕ, d ∣ D → ¬ q ∣ d →
      U q (e d) = a • e d + b • e (d * q)) :
    (∀ d : ℕ, d ∣ D → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
      e d = T (e D)) ∧
    ∀ lam : ℕ → ℂ,
      Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString.solution
