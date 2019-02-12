
import smt.basic

namespace smt

namespace z3

open parser

inductive proof
| elet : string → proof → proof → proof

open sexpr atom parser
-- #check fail
meta def check_fapp (s : string) : sexpr → parser (list sexpr)
| e@(fapp (const (sym x) :: xs)) := xs <$ guard (x = s) <|> parser.fail ("expecting '(" ++ s ++ " ..)' but received " ++ to_string e)
| e := parser.fail $ "expecting '(" ++ s ++ " ..)' but received " ++ to_string e

meta def parse_let : sexpr → parser proof

meta def of_sexpr : sexpr → parser proof
| (fapp [set, el]) := _
| e := parser.fail $ "wrong sexpr: " ++ e.to_string

meta def read_proof : parser proof := parser.sexpr_parser >>= of_sexpr

open tactic

meta def run_proof : proof → tactic unit := _

end z3

meta def z3 : solver :=
{ cmd := "z3",
  args := ["-in", "-smt2"],
  options := [ "(set-option :rlimit 3000)" ],
  -- output_to_file := some "--proof=",
  proof_type := smt.z3.proof,
  read := smt.z3.read_proof,
  execute := smt.z3.run_proof }

end smt
