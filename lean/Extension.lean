import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Extension prompted by Barei (with Muse Spark), Remark 3.5, and the concurrent
Hu--Wen counterexamples (arXiv:2609.25023). The intrinsic three-dimensional
algebra below is NOT asserted to be an evolution algebra. `ambientMul` is
an evolution product on K^5; the injective linear map `embed` preserves
products. Thus its range is a three-dimensional minimal idempotent subspace
of a genuine evolution algebra. The written proof in REPORT.md explains
transport along this embedding and gives the arbitrary-dimensional family.
-/

namespace Extension
variable (K : Type*) [Field K] [CharZero K]
abbrev A := Fin 3 → K
abbrev E := Fin 5 → K

def mul (x y : A K) : A K :=
  ![4*x 0*y 0,
    2*x 0*y 1+2*x 1*y 0+2*x 0*y 2+2*x 2*y 0,
    2*x 0*y 0+2*x 0*y 2+2*x 2*y 0]

def u : A K := ![1,0,0]
def v : A K := ![0,1,0]
def w : A K := ![0,0,1]

def square (U : Submodule K (A K)) : Submodule K (A K) :=
  Submodule.span K {z | ∃ x ∈ U, ∃ y ∈ U, mul K x y = z}

omit [CharZero K] in
theorem product_mem_square {U : Submodule K (A K)} {x y : A K}
    (hx : x ∈ U) (hy : y ∈ U) : mul K x y ∈ square K U :=
  Submodule.subset_span ⟨x,hx,y,hy,rfl⟩

omit [CharZero K] in
theorem top_of_basis_mem (U : Submodule K (A K))
    (hu : u K ∈ U) (hv : v K ∈ U) (hw : w K ∈ U) : U = ⊤ := by
  apply top_unique
  intro y _
  have he : y = y 0 • u K + y 1 • v K + y 2 • w K := by
    ext i; fin_cases i <;> dsimp [u,v,w] <;> ring
  rw [he]
  exact U.add_mem (U.add_mem (U.smul_mem _ hu) (U.smul_mem _ hv)) (U.smul_mem _ hw)

/-- Every subalgebra containing a vector outside the square-zero plane is all of A. -/
theorem generates (U : Submodule K (A K))
    (closed : ∀ x ∈ U, ∀ y ∈ U, mul K x y ∈ U)
    (x : A K) (hx : x ∈ U) (ha : x 0 ≠ 0) : U = ⊤ := by
  let s := mul K x x - (4*x 0) • x
  have hs : s ∈ U := U.sub_mem (closed x hx x hx) (U.smul_mem _ hx)
  have ht : mul K x s - (2*x 0) • s = (4*x 0^3) • v K := by
    ext i; fin_cases i <;> dsimp [s,mul,v] <;> ring
  have hv : v K ∈ U := by
    have hm := U.sub_mem (closed x hx s hs) (U.smul_mem (2*x 0) hs)
    rw [ht] at hm
    exact (Submodule.smul_mem_iff U (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))).mp hm
  have hew : s - (4*x 0*x 2) • v K = (2*x 0^2) • w K := by
    ext i; fin_cases i <;> dsimp [s,mul,v,w] <;> ring
  have hw : w K ∈ U := by
    have hm := U.sub_mem hs (U.smul_mem (4*x 0*x 2) hv)
    rw [hew] at hm
    exact (Submodule.smul_mem_iff U (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))).mp hm
  have heu : x - x 1 • v K - x 2 • w K = x 0 • u K := by
    ext i; fin_cases i <;> dsimp [u,v,w] <;> ring
  have hu : u K ∈ U := by
    have hm := U.sub_mem (U.sub_mem hx (U.smul_mem (x 1) hv)) (U.smul_mem (x 2) hw)
    rw [heu] at hm
    exact (Submodule.smul_mem_iff U ha).mp hm
  exact top_of_basis_mem K U hu hv hw

theorem perfect : square K ⊤ = ⊤ := by
  let U := square K (⊤ : Submodule K (A K))
  have hvv : mul K (u K) (v K) = (2 : K) • v K := by
    ext i; fin_cases i <;> dsimp [mul,u,v] <;> ring
  have hww : mul K (u K) (w K) = (2 : K) • (v K + w K) := by
    ext i; fin_cases i <;> dsimp [mul,u,v,w] <;> ring
  have huu : mul K (u K) (u K) = (4 : K) • u K + (2 : K) • w K := by
    ext i; fin_cases i <;> dsimp [mul,u,w] <;> ring
  have hv : v K ∈ U := by
    have h := product_mem_square K (U := ⊤) (x := u K) (y := v K) (by trivial) (by trivial)
    rw [hvv] at h
    exact (Submodule.smul_mem_iff U (by norm_num : (2 : K) ≠ 0)).mp h
  have hw : w K ∈ U := by
    have h := product_mem_square K (U := ⊤) (x := u K) (y := w K) (by trivial) (by trivial)
    rw [hww] at h
    have h' := (Submodule.smul_mem_iff U (by norm_num : (2 : K) ≠ 0)).mp h
    simpa using U.sub_mem h' hv
  have hu : u K ∈ U := by
    have h := product_mem_square K (U := ⊤) (x := u K) (y := u K) (by trivial) (by trivial)
    rw [huu] at h
    have h' := U.sub_mem h (U.smul_mem (2 : K) hw)
    have h'' : (4 : K) • u K ∈ U := by simpa using h'
    exact (Submodule.smul_mem_iff U (by norm_num : (4 : K) ≠ 0)).mp h''
  exact top_of_basis_mem K U hu hv hw

theorem minimal_idempotent (U : Submodule K (A K))
    (hne : U ≠ ⊥) (hp : square K U = U) : U = ⊤ := by
  classical
  have hex : ∃ x ∈ U, x 0 ≠ 0 := by
    by_contra h
    have hz : ∀ x ∈ U, x 0 = 0 := by simpa using h
    have hs : square K U ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro z ⟨x,hx,y,hy,rfl⟩
      change mul K x y = 0
      ext i; fin_cases i <;> simp [mul,hz x hx,hz y hy]
    exact hne (bot_unique (by simpa [hp] using hs))
  obtain ⟨x,hx,ha⟩ := hex
  apply generates K U _ x hx ha
  intro a ha b hb
  rw [← hp]
  exact product_mem_square K ha hb

theorem idempotent_free (x : A K) (hx : mul K x x = x) : x = 0 := by
  have h0 : 4*x 0*x 0 = x 0 := by simpa [mul] using congrFun hx 0
  have h2 : 2*x 0*x 0+4*x 0*x 2 = x 2 := by
    have h := congrFun hx 2
    dsimp [mul] at h
    linear_combination h
  have ht : x 0*(4*x 0-1)=0 := by linear_combination h0
  have hz : x 0 = 0 := by
    rcases mul_eq_zero.mp ht with h | h
    · exact h
    · have hsq : 2*x 0^2=0 := by linear_combination h2-x 2*h
      have hs : x 0^2=0 := (mul_eq_zero.mp hsq).resolve_left (by norm_num)
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs
  have h1 := congrFun hx 1
  have hy : x 1 = 0 := by simpa [mul,hz] using h1.symm
  have hw : x 2 = 0 := by simpa [hz] using h2.symm
  ext i; fin_cases i <;> simp [hz,hy,hw]

/-- Coordinates (a,b,c) map to a*u+b*v+c*w in the five-dimensional ambient space. -/
def embed : A K →ₗ[K] E K where
  toFun x := ![x 0,x 0+x 1,x 0-x 1,x 0+x 2,x 0-x 2]
  map_add' x y := by ext i; fin_cases i <;> dsimp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> dsimp <;> ring

omit [CharZero K] in
theorem embed_injective : Function.Injective (embed K) := by
  intro x y h
  have h0 : x 0=y 0 := by simpa [embed] using congrFun h 0
  have h1 : x 0+x 1=y 0+y 1 := by simpa [embed] using congrFun h 1
  have h2 : x 0+x 2=y 0+y 2 := by simpa [embed] using congrFun h 3
  ext i; fin_cases i
  · exact h0
  · change x 1 = y 1
    linear_combination h1-h0
  · change x 2 = y 2
    linear_combination h2-h0

/-- Columns of the structure matrix are (4,4,4,6,2), v,-v,v+w,-v-w. -/
def ambientMul (x y : E K) : E K :=
  ![4*x 0*y 0,
    4*x 0*y 0+x 1*y 1-x 2*y 2+x 3*y 3-x 4*y 4,
    4*x 0*y 0-x 1*y 1+x 2*y 2-x 3*y 3+x 4*y 4,
    6*x 0*y 0+x 3*y 3-x 4*y 4,
    2*x 0*y 0-x 3*y 3+x 4*y 4]

omit [CharZero K] in
theorem embedding_preserves_product (x y : A K) :
    ambientMul K (embed K x) (embed K y) = embed K (mul K x y) := by
  ext i; fin_cases i <;> dsimp [ambientMul,embed,mul] <;>
    (try simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]) <;> ring

omit [CharZero K] in
theorem ambient_evolution (i j : Fin 5) (h : i ≠ j) :
    ambientMul K (fun k => if k=i then 1 else 0) (fun k => if k=j then 1 else 0) = 0 := by
  ext k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [ambientMul]

def ambientSquare (U : Submodule K (E K)) : Submodule K (E K) :=
  Submodule.span K {z | ∃ x ∈ U, ∃ y ∈ U, ambientMul K x y = z}

def V : Submodule K (E K) := (embed K).range

omit [CharZero K] in
theorem ambient_product_mem {U : Submodule K (E K)} {x y : E K}
    (hx : x ∈ U) (hy : y ∈ U) : ambientMul K x y ∈ ambientSquare K U :=
  Submodule.subset_span ⟨x,hx,y,hy,rfl⟩

theorem ambient_perfect : ambientSquare K (V K) = V K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    rw [embedding_preserves_product]
    exact LinearMap.mem_range_self _ _
  · have hle : square K ⊤ ≤ (ambientSquare K (V K)).comap (embed K) := by
      apply Submodule.span_le.mpr
      rintro z ⟨x,_,y,_,rfl⟩
      change embed K (mul K x y) ∈ ambientSquare K (V K)
      rw [← embedding_preserves_product]
      exact ambient_product_mem K (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    rw [perfect K] at hle
    intro z hz
    obtain ⟨a,rfl⟩ := hz
    exact hle (by trivial)

theorem ambient_generates (U : Submodule K (E K)) (hUV : U ≤ V K)
    (closed : ∀ x ∈ U, ∀ y ∈ U, ambientMul K x y ∈ U)
    (x : E K) (hx : x ∈ U) (ha : x 0 ≠ 0) : U = V K := by
  obtain ⟨a,he⟩ := hUV hx
  let C := U.comap (embed K)
  have hac : a ∈ C := by change embed K a ∈ U; rwa [he]
  have ha0 : a 0 ≠ 0 := by
    have h : (embed K a) 0 = x 0 := congrFun he 0
    simpa [embed] using h.trans_ne ha
  have hC : C = ⊤ := by
    apply generates K C _ a hac ha0
    intro b hb c hc
    change embed K (mul K b c) ∈ U
    rw [← embedding_preserves_product]
    exact closed _ hb _ hc
  apply le_antisymm hUV
  intro z hz
  obtain ⟨b,rfl⟩ := hz
  have h : b ∈ C := by rw [hC]; trivial
  exact h

theorem ambient_minimal (U : Submodule K (E K))
    (hUV : U ≤ V K) (hne : U ≠ ⊥) (hp : ambientSquare K U = U) : U = V K := by
  classical
  have hex : ∃ x ∈ U, x 0 ≠ 0 := by
    by_contra h
    have hz : ∀ x ∈ U, x 0 = 0 := by simpa using h
    have hs : ambientSquare K U ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro z ⟨x,hx,y,hy,rfl⟩
      change ambientMul K x y = 0
      obtain ⟨a,hea⟩ := hUV hx
      obtain ⟨b,heb⟩ := hUV hy
      have ha : a 0=0 := by simpa [embed] using (congrFun hea 0).trans (hz x hx)
      have hb : b 0=0 := by simpa [embed] using (congrFun heb 0).trans (hz y hy)
      rw [← hea,← heb,embedding_preserves_product]
      have hm : mul K a b=0 := by ext i; fin_cases i <;> simp [mul,ha,hb]
      rw [hm,map_zero]
    exact hne (bot_unique (by simpa [hp] using hs))
  obtain ⟨x,hx,ha⟩ := hex
  apply ambient_generates K U hUV _ x hx ha
  intro a ha b hb
  rw [← hp]
  exact ambient_product_mem K ha hb

theorem ambient_nonzero : V K ≠ ⊥ := by
  intro h
  have hm : embed K (u K) ∈ V K := LinearMap.mem_range_self _ _
  rw [h,Submodule.mem_bot] at hm
  have hc := congrFun hm 0
  simp [embed,u] at hc

theorem complex_ambient_certificate :
    V ℂ ≠ ⊥ ∧ ambientSquare ℂ (V ℂ) = V ℂ ∧
    ∀ U : Submodule ℂ (E ℂ), U ≤ V ℂ → U ≠ ⊥ → ambientSquare ℂ U = U → U = V ℂ :=
  ⟨ambient_nonzero ℂ,ambient_perfect ℂ,fun U hUV hne hp => ambient_minimal ℂ U hUV hne hp⟩

theorem complex_minimal_idempotent :
    square ℂ ⊤ = ⊤ ∧
    ∀ U : Submodule ℂ (A ℂ), U ≠ ⊥ → square ℂ U = U → U = ⊤ :=
  ⟨perfect ℂ, fun U h hp => minimal_idempotent ℂ U h hp⟩

end Extension

#print axioms Extension.complex_minimal_idempotent
#print axioms Extension.embedding_preserves_product
#print axioms Extension.complex_ambient_certificate
