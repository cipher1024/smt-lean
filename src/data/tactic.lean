import tactic.basic

namespace tactic

meta def mk_has_repr_instance : tactic unit :=
do refine ``( { repr := _ } ),
   x ← intro1,
   xs ← induction x,
   xs.mmap' $ λ x,
     do guard x.2.1.empty <|> fail "can only derive `has_repr` for enumerated types",
        let s := to_string (x.1.update_prefix name.anonymous),
        exact $ reflect s

@[derive_handler] meta def has_reflect_derive_handler :=
instance_derive_handler ``has_repr mk_has_repr_instance ff

end tactic
