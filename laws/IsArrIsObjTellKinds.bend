# For every value `j`, `is_arr(j)` is true exactly when `j` is an array and
# `is_obj(j)` exactly when `j` is an object: `is_arr(arr(xs))` and
# `is_obj(obj(ps))` hold, and neither holds of a null, a boolean, a number or
# a string, owned or a span
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/ArrayAccess.bend as D1
import ./defs/ObjectTest.bend as D2

# LAW: is_arr holds of a value exactly when it is an array
law is_arr_kind:
  for +val: V.Json
  {Ezjson.is_arr(val) == D1.is_arr(val) : Bool}

# LAW: is_obj holds of a value exactly when it is an object
law is_obj_kind:
  for +val: V.Json
  {Ezjson.is_obj(val) == D2.is_obj(val) : Bool}

# LAW: an array built from any list is an array and not an object
law is_arr_arr:
  for xs: List<&2, V.Json>
  {Bool.and(Ezjson.is_arr(Ezjson.arr(xs)), Bool.not(Ezjson.is_obj(Ezjson.arr(xs)))) == True{} : Bool}

# LAW: an object built from any pairs is an object and not an array
law is_obj_obj:
  for ps: List<&1, String & V.Json>
  {Bool.and(Ezjson.is_obj(Ezjson.obj(ps)), Bool.not(Ezjson.is_arr(Ezjson.obj(ps)))) == True{} : Bool}
