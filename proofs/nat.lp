require open proofs.bool

// Data type of natural numbers.

symbol const N : TYPE

symbol const z : N
symbol const s : N ⇒ N

// Enabling built-in natural number literal, and example.

set builtin "0"  ≔ z
set builtin "+1" ≔ s

definition forty_two ≔ 42

// Addition function.

symbol add : N ⇒ N ⇒ N
set binop "+" ≔ add

rule z      + &n     → &n
rule (s &m) + &n     → s (&m + &n)
rule &m     + z      → &m
rule &m     + (s &n) → s (&m + &n)

// Multiplication function.

symbol mul : N ⇒ N ⇒ N
set binop "×" ≔ mul

rule z      × _      → z
rule (s &m) × &n     → &n + (&m × &n)
rule _      × z      → z
rule &m     × (s &n) → &m + (&m × &n)

// Doubling function.

definition double n ≔ mul n 2

// Equality function.

symbol eq_nat : N ⇒ N ⇒ B

rule eq_nat z      z      → true
rule eq_nat (s &m) (s &n) → eq_nat &m &n
rule eq_nat z      (s _)  → false
rule eq_nat (s _)  z      → false

// Less than function.

symbol le_nat : N ⇒ N ⇒ B

rule le_nat z      z      → false
rule le_nat z      (s _)  → true
rule le_nat (s &m) (s &n) → le_nat &m &n
