theory Chapter_1
  imports Main

begin
(*
datatype bool = True | False
*)
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor a b = (a \<noteq> b)"

value "xor True True"
value "xor True False"
value "xor False True"
value "xor False False"

end