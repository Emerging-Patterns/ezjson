# `at(arr(xs), i)` is the `i`-th element of `xs` when `i` is less than its
# length, and `null()` otherwise; `at(j, i)` is `null()` for every `j` that is
# not an array
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/ArrayAccess.bend as D1

# LAW: at on a value that is not an array is null, at every index
law at_not_arr:
  for +val: V.Json
  for idx: U32
  for h_kind: {D1.is_arr(val) == False{} : Bool}
  {Ezjson.at(val, idx) == Ezjson.null() : V.Json}

# LAW: at on an array is the element at that index, and null past the end
law at_arr:
  for +xs: List<&2, V.Json>
  for idx: U32
  {Ezjson.at(Ezjson.arr(xs), idx) == D1.nth(xs, U32.to_nat(idx)) : V.Json}
