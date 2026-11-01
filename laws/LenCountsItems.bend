# `len(arr(xs))` is the length of `xs`, `len(obj(ps))` the length of `ps`, and
# `len(j)` is 0 for every scalar
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/ArrayAccess.bend as D1
import ./defs/ObjectTest.bend as D2

# LAW: len of an array is how many elements built it
law len_arr:
  for xs: List<&2, V.Json>
  {Ezjson.len(Ezjson.arr(xs)) == U32.from_nat(List.length(&2, V.Json, xs)) : U32}

# LAW: len of an object is how many pairs built it
law len_obj:
  for ps: List<&1, String & V.Json>
  {Ezjson.len(Ezjson.obj(ps)) == U32.from_nat(List.length(&1, String & V.Json, ps)) : U32}

# LAW: len is 0 on every value that is neither an array nor an object
law len_scalar:
  for +val: V.Json
  for h_arr: {D1.is_arr(val) == False{} : Bool}
  for h_obj: {D2.is_obj(val) == False{} : Bool}
  {Ezjson.len(val) == 0 : U32}
