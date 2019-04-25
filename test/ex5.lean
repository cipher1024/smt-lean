import «smt-lean»

example {α : Type} {z : α} {x y : list α}
  (h : (z :: x : list α) = z :: y)
 : x = y :=
begin
  veriT,
end
