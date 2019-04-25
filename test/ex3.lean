import «smt-lean»

section some_algorithm

open smt.logic_fragment

variables n x n' x' : ℤ
variables Act₀ : n' = n + 1
variables Act₁ : x' = x + 3*n^2 + 3*n + 1
variables J₀ : x = n^3

include J₀ Act₀ Act₁
example : x' = n'^3 :=
by { -- subst n', subst x', norm_num [right_distrib,left_distrib],
     veriT (QF_NIA) }

end some_algorithm
