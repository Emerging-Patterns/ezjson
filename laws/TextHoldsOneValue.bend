# For texts shorter than 2^32 - 1 characters: for every two well-formed values
# `j` and `k`, `parse(print(j) ++ " " ++ print(k))` is `None`: a text holds
# exactly one value (§2)
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: a text of two values does not parse: a text holds exactly one value
law two_none:
  for +jj: V.Json
  for +kk: V.Json
  for +h_j: {V.wf(jj) == True{} : Bool}
  for +h_k: {V.wf(kk) == True{} : Bool}
  for h_s: {D1.short(Ezjson.print(jj) ++ " " ++ Ezjson.print(kk)) == True{} : Bool}
  {Ezjson.parse(Ezjson.print(jj) ++ " " ++ Ezjson.print(kk)) == None{} : Maybe<&2, V.Json>}
