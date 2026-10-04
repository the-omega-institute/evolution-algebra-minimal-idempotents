import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Certificate of Example 2.1 of Andres Barei (with Muse Spark via meta.ai),
reviewed by Nicolás Jaramillo Torres, manuscript dated 2026-10-02.
Concurrent counterexamples: Xing-Yu Hu and Ran Wen, arXiv:2609.25023.
The example and its priority are theirs; this file certifies it.

Coordinates refer to the natural basis e1,e2,e3. Products are bilinear,
commutative, and not presumed associative. `square V` is the linear span
of ALL products of pairs of elements of V, exactly as in §2 of the paper.
`derived n` denotes E^(n+1), so `Solvable` is precisely termination of
the paper's positive-indexed derived series, including E^(1).
-/

namespace Barei

variable (K : Type*) [Field K]

abbrev E := Fin 3 → K

def mul (x y : E K) : E K :=
  ![-2 * x 0 * y 0,
    x 1 * y 1 - x 2 * y 2,
    2 * x 0 * y 0 - x 1 * y 1 + x 2 * y 2]

theorem mul_comm (x y : E K) : mul K x y = mul K y x := by
  ext i; fin_cases i <;> simp [mul] <;> ring

theorem mul_add (x y z : E K) : mul K (x + y) z = mul K x z + mul K y z := by
  ext i; fin_cases i <;> simp [mul] <;> ring

theorem mul_smul (a : K) (x y : E K) : mul K (a • x) y = a • mul K x y := by
  ext i; fin_cases i <;> simp [mul] <;> ring

def e (i : Fin 3) : E K := fun j => if j = i then 1 else 0

noncomputable def naturalBasis : Module.Basis (Fin 3) K (E K) := Pi.basisFun K (Fin 3)

theorem naturalBasis_eq (i : Fin 3) : naturalBasis K i = e K i := by
  ext j
  simp [naturalBasis,Pi.basisFun_apply,Pi.single,Function.update,e,eq_comm]

theorem natural_basis_products (i j : Fin 3) (h : i ≠ j) :
    mul K (e K i) (e K j) = 0 := by
  ext k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [mul, e]

def r1 : E K := ![-2, 0, 2]
def r2 : E K := ![0, 1, -1]

theorem basis_squares :
    mul K (e K 0) (e K 0) = r1 K ∧
    mul K (e K 1) (e K 1) = r2 K ∧
    mul K (e K 2) (e K 2) = -r2 K := by
  constructor
  · ext i; fin_cases i <;> simp [mul, e, r1]
  constructor <;> ext i <;> fin_cases i <;> simp [mul, e, r2]

def square (V : Submodule K (E K)) : Submodule K (E K) :=
  Submodule.span K {z | ∃ x ∈ V, ∃ y ∈ V, mul K x y = z}

def derived : ℕ → Submodule K (E K)
  | 0 => ⊤
  | n + 1 => square K (derived n)

def Solvable : Prop := ∃ n : ℕ, derived K n = ⊥

def IdempotentFree : Prop := ∀ x : E K, mul K x x = x → x = 0

theorem product_mem_square {V : Submodule K (E K)} {x y : E K}
    (hx : x ∈ V) (hy : y ∈ V) : mul K x y ∈ square K V :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem r1r1 : mul K (r1 K) (r1 K) = (4 : K) • (r1 K - r2 K) := by
  ext i; fin_cases i <;> dsimp [mul, r1, r2] <;> ring

theorem r1r2 : mul K (r1 K) (r2 K) = (2 : K) • r2 K := by
  ext i; fin_cases i <;> dsimp [mul, r1, r2] <;> ring

theorem r2r2 : mul K (r2 K) (r2 K) = 0 := by
  ext i; fin_cases i <;> simp [mul, r2]

variable [NeZero (2 : K)]

theorem persistent_vectors (n : ℕ) : r1 K ∈ derived K n ∧ r2 K ∈ derived K n := by
  induction n with
  | zero => simp [derived]
  | succ n ih =>
    change r1 K ∈ square K (derived K n) ∧ r2 K ∈ square K (derived K n)
    have htwo : (2 : K) ≠ 0 := NeZero.ne _
    have hfour : (4 : K) ≠ 0 := by
      have h : (4 : K) = 2 * 2 := by ring
      rw [h]; exact mul_ne_zero htwo htwo
    have h12 := product_mem_square K ih.1 ih.2
    rw [r1r2] at h12
    have h2 : r2 K ∈ square K (derived K n) :=
      (Submodule.smul_mem_iff _ htwo).mp h12
    have h11 := product_mem_square K ih.1 ih.1
    rw [r1r1] at h11
    have hdiff : r1 K - r2 K ∈ square K (derived K n) :=
      (Submodule.smul_mem_iff _ hfour).mp h11
    exact ⟨by simpa using (square K (derived K n)).add_mem hdiff h2, h2⟩

theorem not_solvable : ¬ Solvable K := by
  rintro ⟨n, hn⟩
  have h := (persistent_vectors K n).2
  rw [hn, Submodule.mem_bot] at h
  have hc := congrFun h 1
  simp [r2] at hc

omit [NeZero (2 : K)] in
theorem idempotent_free : IdempotentFree K := by
  intro x hx
  have h0 : -2 * x 0 * x 0 = x 0 := by simpa [mul] using congrFun hx 0
  have h1 : x 1 * x 1 - x 2 * x 2 = x 1 := by simpa [mul] using congrFun hx 1
  have h2 : 2 * x 0 * x 0 - x 1 * x 1 + x 2 * x 2 = x 2 := by
    simpa [mul] using congrFun hx 2
  have hs : x 0 + x 1 + x 2 = 0 := by linear_combination -h0 - h1 - h2
  have ht : x 0 * (1 + 2 * x 0) = 0 := by linear_combination -h0
  have hu : (1 + 2 * x 0) * x 1 + x 0 ^ 2 = 0 := by
    linear_combination -h1 + (x 1 - x 2 + x 0) * hs
  have hx0 : x 0 = 0 := by
    rcases mul_eq_zero.mp ht with h | h
    · exact h
    · rw [h, zero_mul, zero_add] at hu
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hu
  have hx1 : x 1 = 0 := by simpa [hx0] using hu
  have hx2 : x 2 = 0 := by simpa [hx0, hx1] using hs
  ext i; fin_cases i <;> simp [hx0, hx1, hx2]

theorem counterexample : ¬ Solvable K ∧ IdempotentFree K :=
  ⟨not_solvable K, idempotent_free K⟩

theorem complex_counterexample : ¬ Solvable ℂ ∧ IdempotentFree ℂ := counterexample ℂ

theorem refutes_conjecture_1_1 : ¬ (Solvable ℂ ↔ IdempotentFree ℂ) := by
  intro h
  exact not_solvable ℂ (h.mpr (idempotent_free ℂ))

end Barei

#print axioms Barei.counterexample
#print axioms Barei.complex_counterexample
#print axioms Barei.refutes_conjecture_1_1
