import «smt-lean»

example {x y : ℤ} (h1 : ((x - y) = (x + (- y) + 2)))
 : false :=
begin
  veriT,
end
