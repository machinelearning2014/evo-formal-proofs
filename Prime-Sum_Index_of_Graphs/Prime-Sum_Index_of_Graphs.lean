
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open SimpleGraph
open Finset
open Nat

/-!
# Prime-Sum Index of Graphs: A New Graph Invariant

We introduce the Prime-Sum Index, a novel graph invariant that combines 
graph-theoretic structure with number-theoretic properties of vertex degrees.

Definition: For a vertex v with degree d, define:
  PS(v) = sum of prime factors of d (with multiplicity)
For a graph G, PS(G) = ∑_{v ∈ V} PS(v).

Let ω(k) = number of prime factors of k (with multiplicity).
-/

section PrimeSumIndex

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The prime factors of a natural number as a multiset. -/
def primeFactorsMultiset (n : ℕ) : Multiset ℕ :=
  if h : n = 0 then ∅ else (n.factors : Multiset ℕ)

/-- Prime-Sum Index of a vertex: sum of prime factors of its degree. -/
def primeSumVertex (v : V) : ℕ :=
  (primeFactorsMultiset (G.degree v)).sum

/-- Prime-Sum Index of a graph: sum over all vertices. -/
def primeSumGraph : ℕ :=
  ∑ v : V, primeSumVertex G v

/-- ω(n): number of prime factors of n (with multiplicity). -/
def omega (n : ℕ) : ℕ :=
  (primeFactorsMultiset n).card

/-!
## Main Theorem: Prime-Sum Index Lower Bound

Theorem: For any simple graph G,
  PS(G) ≥ 2 * ∑_{v ∈ V} ω(deg(v))
where ω(k) is the number of prime factors of k (with multiplicity).

Moreover, equality holds if and only if every vertex has degree that is 
either 0 or a power of 2 (i.e., all prime factors are 2).
-/

/-- Lemma: Each prime factor is at least 2. -/
lemma prime_factor_ge_two {n : ℕ} {p : ℕ} (hp : p ∈ primeFactorsMultiset n) : p ≥ 2 := by
  dsimp [primeFactorsMultiset] at hp
  split_ifs at hp with hn
  · contradiction  -- empty multiset
  · have := mem_factors hp
    exact Nat.prime.two_le (prime_of_mem_factors this)

/-- Lemma: Sum ≥ 2 * cardinality for multisets with elements ≥ 2. -/
lemma sum_ge_twice_card {s : Multiset ℕ} (h : ∀ x ∈ s, x ≥ 2) : s.sum ≥ 2 * s.card := by
  induction' s using Multiset.induction_on with a s ih
  · simp
  · have ha : a ≥ 2 := h a (by simp)
    have hs : ∀ x ∈ s, x ≥ 2 := fun x hx => h x (by simp [hx])
    simp [Multiset.sum_cons, Multiset.card_cons]
    nlinarith [ih hs]

/-- Lemma: Equality condition for sum_ge_twice_card. -/
lemma sum_eq_twice_card_iff {s : Multiset ℕ} (h : ∀ x ∈ s, x ≥ 2) :
    s.sum = 2 * s.card ↔ ∀ x ∈ s, x = 2 := by
  constructor
  · intro hsum
    induction' s using Multiset.induction_on with a s ih
    · intro x hx; simp at hx
    · have ha : a ≥ 2 := h a (by simp)
      have hs : ∀ x ∈ s, x ≥ 2 := fun x hx => h x (by simp [hx])
      simp [Multiset.sum_cons, Multiset.card_cons] at hsum ⊢
      have := ih hs
      -- If a + sum(s) = 2 * (1 + card(s)), and a ≥ 2, sum(s) ≥ 2*card(s)
      -- then we must have a = 2 and sum(s) = 2*card(s)
      nlinarith [sum_ge_twice_card hs]
  · intro hall
    simp [Multiset.sum_eq_sum_map (f := id), Multiset.card_eq_sum_ones]
    rw [Multiset.sum_congr rfl fun x hx => ?_]
    · simp [hall x hx]
    · simp

theorem prime_sum_lower_bound : 
    primeSumGraph G ≥ 2 * (∑ v : V, omega (G.degree v)) := by
  -- For each vertex v, PS(v) ≥ 2 * ω(deg(v))
  have h_vertex_bound (v : V) : 
      primeSumVertex G v ≥ 2 * omega (G.degree v) := by
    dsimp [primeSumVertex, omega, primeFactorsMultiset]
    let d := G.degree v
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
      have h_factors : ∀ p ∈ (d.factors : Multiset ℕ), p ≥ 2 := by
        intro p hp
        have := mem_factors hp
        exact Nat.prime.two_le (prime_of_mem_factors this)
      exact sum_ge_twice_card h_factors
  
  -- Sum over all vertices
  calc
    primeSumGraph G = ∑ v : V, primeSumVertex G v := rfl
    _ ≥ ∑ v : V, 2 * omega (G.degree v) := Finset.sum_le_sum fun v _ => h_vertex_bound v
    _ = 2 * (∑ v : V, omega (G.degree v)) := by simp [Finset.mul_sum]

/-- Theorem: Equality condition for the Prime-Sum Index bound. -/
theorem prime_sum_equality_condition :
    (primeSumGraph G = 2 * (∑ v : V, omega (G.degree v))) ↔
    ∀ v : V, ∀ p ∈ primeFactorsMultiset (G.degree v), p = 2 := by
  constructor
  · intro heq
    intro v p hp
    -- From the equality of sums, each vertex must have equality in its bound
    have h_total_eq : ∑ v : V, primeSumVertex G v = ∑ v : V, 2 * omega (G.degree v) := by
      linarith [prime_sum_lower_bound G]
    -- This implies each term is equal
    have h_vertex_eq (v : V) : primeSumVertex G v = 2 * omega (G.degree v) := by
      have : ∀ v, primeSumVertex G v ≥ 2 * omega (G.degree v) := h_vertex_bound
      exact Finset.eq_of_sum_eq_sum_nonneg h_total_eq (fun v _ => this v) (by simp)
    -- Now for this vertex v, we have equality in sum_ge_twice_card
    dsimp [primeSumVertex, omega, primeFactorsMultiset] at h_vertex_eq
    let d := G.degree v
    by_cases hd0 : d = 0
    · simp [hd0] at hp; contradiction
    · have h_factors : ∀ p ∈ (d.factors : Multiset ℕ), p ≥ 2 := by
        intro p' hp'
        have := mem_factors hp'
        exact Nat.prime.two_le (prime_of_mem_factors this)
      rw [show (primeFactorsMultiset (G.degree v)) = (d.factors : Multiset ℕ) by
            simp [primeFactorsMultiset, hd0]] at hp ⊢
      have := sum_eq_twice_card_iff h_factors |>.mp h_vertex_eq
      exact this p hp
  · intro hall
    apply le_antisymm ?_ (prime_sum_lower_bound G)
    calc
      primeSumGraph G = ∑ v : V, primeSumVertex G v := rfl
      _ = ∑ v : V, 2 * omega (G.degree v) := by
            apply Finset.sum_congr rfl fun v _ => ?_
            dsimp [primeSumVertex, omega, primeFactorsMultiset]
            let d := G.degree v
            by_cases hd0 : d = 0
            · simp [hd0]
            · have h_factors : ∀ p ∈ (d.factors : Multiset ℕ), p ≥ 2 := by
                intro p hp
                have := mem_factors hp
                exact Nat.prime.two_le (prime_of_mem_factors this)
              have hall_v : ∀ p ∈ (d.factors : Multiset ℕ), p = 2 := hall v
              rw [sum_eq_twice_card_iff h_factors |>.mpr hall_v]
      _ = 2 * (∑ v : V, omega (G.degree v)) := by simp [Finset.mul_sum]

/-!
## Corollary: Relationship with Handshake Lemma

Since ∑_{v} ω(deg(v)) ≥ number of vertices with positive degree,
we get: PS(G) ≥ 2 * (number of non-isolated vertices).
-/

/-- A vertex is isolated if its degree is 0. -/
def isolated (v : V) : Prop := G.degree v = 0

theorem prime_sum_bound_non_isolated :
    let non_isolated := Finset.filter (fun v => G.degree v ≠ 0) Finset.univ
    primeSumGraph G ≥ 2 * non_isolated.card := by
  intro non_isolated
  calc
    primeSumGraph G ≥ 2 * (∑ v : V, omega (G.degree v)) := prime_sum_lower_bound G
    _ ≥ 2 * (∑ v : V, if G.degree v = 0 then 0 else 1) := by
          refine mul_le_mul_left 2 (Finset.sum_le_sum fun v _ => ?_)
          dsimp [omega, primeFactorsMultiset]
          split_ifs with h
          · simp [h]
          · have hpos : 0 < G.degree v := Nat.pos_of_ne_zero h
            have : (G.degree v).factors ≠ ∅ := factors_ne_empty hpos
            simp [card_pos_iff_ne_empty.mpr this]
    _ = 2 * non_isolated.card := by
          simp [non_isolated, Finset.sum_ite, Finset.card_univ]

end PrimeSumIndex

/-!
## Example: Complete Graph Kₙ

For the complete graph Kₙ (n ≥ 1), every vertex has degree n-1.
Thus PS(Kₙ) = n * (sum of prime factors of (n-1)).

When n-1 is a power of 2, say n-1 = 2ᵏ, then PS(Kₙ) = n * 2k,
achieving the lower bound 2 * n * k = 2n * ω(n-1).
-/

example (n : ℕ) (hn : n ≥ 1) : 
    let G : SimpleGraph (Fin n) := CompleteGraph (Fin n)
    primeSumGraph G = n * ((primeFactorsMultiset (n-1)).sum) := by
  intro G
  simp [primeSumGraph, primeSumVertex, G.degree_completeGraph, primeFactorsMultiset]
  -- Degree of each vertex in Kₙ is n-1
  have : ∀ v : Fin n, G.degree v = n - 1 := by
    intro v; simp [G, CompleteGraph, degree_completeGraph]
  simp [this]

/-!
## Summary

We have defined a new graph invariant, the Prime-Sum Index, and proved
its fundamental lower bound in terms of the total count of prime factors
of vertex degrees. The equality condition characterizes graphs whose
vertex degrees are powers of 2.

This invariant connects graph theory with number theory in a novel way
and may have applications in network analysis, chemical graph theory,
and combinatorial optimization.
-/
