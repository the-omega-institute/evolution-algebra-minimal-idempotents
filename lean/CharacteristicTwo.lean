import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
A characteristic-two extension of the questions in Barei (with Muse Spark)
and Hu--Wen (arXiv:2609.25023). This is a different evolution algebra from
Barei's Example 2.1. Its natural-basis squares are (0,1,1), (0,1,1), (1,0,1).
All assertions hold over EVERY field with 2=0, including its algebraic closure.
Derived terms and solvability use precisely the paper's definition, with
`derived n = E^(n+1)`. No associativity is assumed.
-/

namespace CharacteristicTwo
variable (K : Type*) [Field K]
abbrev E := Fin 3 → K

def mul (x y : E K) : E K :=
  ![x 2*y 2, x 0*y 0+x 1*y 1, x 0*y 0+x 1*y 1+x 2*y 2]

def u : E K := ![0,1,1]
def v : E K := ![1,1,0]

def square (U : Submodule K (E K)) : Submodule K (E K) :=
  Submodule.span K {z | ∃ x ∈ U, ∃ y ∈ U, mul K x y = z}

def derived : ℕ → Submodule K (E K)
  | 0 => ⊤
  | n+1 => square K (derived n)

def Solvable : Prop := ∃ n, derived K n = ⊥
def IdempotentFree : Prop := ∀ x : E K, mul K x x = x → x = 0

theorem product_mem_square {U : Submodule K (E K)} {x y : E K}
    (hx : x ∈ U) (hy : y ∈ U) : mul K x y ∈ square K U :=
  Submodule.subset_span ⟨x,hx,y,hy,rfl⟩

theorem mul_comm (x y : E K) : mul K x y = mul K y x := by
  ext i; fin_cases i <;> dsimp [mul] <;> ring
theorem mul_add (x y z : E K) : mul K (x+y) z = mul K x z+mul K y z := by
  ext i; fin_cases i <;> dsimp [mul] <;> ring
theorem mul_smul (a : K) (x y : E K) : mul K (a • x) y = a • mul K x y := by
  ext i; fin_cases i <;> dsimp [mul] <;> ring
theorem natural_products (i j : Fin 3) (h : i ≠ j) :
    mul K (fun k => if k=i then 1 else 0) (fun k => if k=j then 1 else 0) = 0 := by
  ext k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [mul]

variable (hchar : (2 : K) = 0)
include hchar

theorem uu : mul K (u K) (u K) = v K := by
  ext i; fin_cases i <;> dsimp [mul,u,v]
  · ring
  · ring
  · linear_combination hchar

omit hchar in
theorem uv : mul K (u K) (v K) = u K := by
  ext i; fin_cases i <;> dsimp [mul,u,v] <;> ring

theorem vv : mul K (v K) (v K) = 0 := by
  ext i; fin_cases i <;> dsimp [mul,v]
  · ring
  · linear_combination hchar
  · linear_combination hchar

theorem persistent (n : ℕ) : u K ∈ derived K n ∧ v K ∈ derived K n := by
  induction n with
  | zero => simp [derived]
  | succ n ih =>
    change u K ∈ square K (derived K n) ∧ v K ∈ square K (derived K n)
    constructor
    · have h := product_mem_square K ih.1 ih.2
      rwa [uv] at h
    · have h := product_mem_square K ih.1 ih.1
      rwa [uu K hchar] at h

theorem not_solvable : ¬ Solvable K := by
  rintro ⟨n,hn⟩
  have h := (persistent K hchar n).1
  rw [hn,Submodule.mem_bot] at h
  have hc := congrFun h 1
  simp [u] at hc

theorem idempotent_free : IdempotentFree K := by
  intro x hx
  have h0 : x 2*x 2=x 0 := by simpa [mul] using congrFun hx 0
  have h1 : x 0*x 0+x 1*x 1=x 1 := by simpa [mul] using congrFun hx 1
  have h2 : x 0*x 0+x 1*x 1+x 2*x 2=x 2 := by simpa [mul] using congrFun hx 2
  have hs : x 2-x 0-x 1=0 := by linear_combination -h2+h0+h1
  have hxy : x 0-x 1=0 := by
    linear_combination -h0+h1+(x 2+x 0+x 1)*hs+x 0*x 1*hchar
  have hz : x 2=0 := by linear_combination hs-hxy+x 0*hchar
  have ha : x 0=0 := by simpa [hz] using h0.symm
  have hb : x 1=0 := by linear_combination ha-hxy
  ext i; fin_cases i <;> simp [ha,hb,hz]

theorem counterexample : ¬ Solvable K ∧ IdempotentFree K :=
  ⟨not_solvable K hchar,idempotent_free K hchar⟩

end CharacteristicTwo

#print axioms CharacteristicTwo.counterexample
