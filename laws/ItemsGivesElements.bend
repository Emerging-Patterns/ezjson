# `items(arr(xs))` is `xs`; for every well-formed array `j`, `arr(items(j))`
# is `j`, `at(j, i)` is the `i`-th element of `items(j)` (`null()` past its
# end) and `len(j)` is the length of `items(j)`: `items` gives an array's
# elements in order; `items(j)` is `[]` for every `j` that is not an array
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/ArrayAccess.bend as D1

# LAW: items of an array built from a list is that list
law items_arr:
  for xs: List<&2, V.Json>
  {Ezjson.items(Ezjson.arr(xs)) == xs : List<&2, V.Json>}

# LAW: a well-formed array is the array built from its items
law items_back:
  for +val: V.Json
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_arr: {D1.is_arr(val) == True{} : Bool}
  {Ezjson.arr(Ezjson.items(val)) == val : V.Json}

# LAW: at on a well-formed array is the element of its items at that index,
# and null past the end
law items_at:
  for +val: V.Json
  for +idx: U32
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_arr: {D1.is_arr(val) == True{} : Bool}
  {Ezjson.at(val, idx) == D1.nth(Ezjson.items(val), U32.to_nat(idx)) : V.Json}

# LAW: len of a well-formed array is how many items it has
law items_len:
  for +val: V.Json
  for +h_wf: {V.wf(val) == True{} : Bool}
  for h_arr: {D1.is_arr(val) == True{} : Bool}
  {Ezjson.len(val) == U32.from_nat(List.length(&2, V.Json, Ezjson.items(val))) : U32}

# LAW: items of a value that is not an array is empty
law items_not_arr:
  for +val: V.Json
  for h_kind: {D1.is_arr(val) == False{} : Bool}
  {Ezjson.items(val) == [] : List<&2, V.Json>}
