# For texts shorter than 2^32 - 1 characters: for every text `t` with
# `parse(t) == Some{j}`, every reader (`get`, `at`, `as_*`) gives on `j` the
# result it gives on the owned value `same` as `j`: a span reads as its
# characters
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ./defs/CursorAndNumberRules.bend as D1

# LAW: get reads a value as it reads the value with its spans read out
law get_same:
  for +val: V.Json
  for +key: String
  {D1.own(Ezjson.get(val, key)) == Ezjson.get(D1.own(val), key) : V.Json}

# LAW: at reads a value as it reads the value with its spans read out
law at_same:
  for +val: V.Json
  for +idx: U32
  {D1.own(Ezjson.at(val, idx)) == Ezjson.at(D1.own(val), idx) : V.Json}

# LAW: as_str reads a span as its characters
law as_str_same:
  for +val: V.Json
  {Ezjson.as_str(val) == Ezjson.as_str(D1.own(val)) : Maybe<&2, String>}

# LAW: as_bool reads a value as it reads the value with its spans read out
law as_bool_same:
  for +val: V.Json
  {Ezjson.as_bool(val) == Ezjson.as_bool(D1.own(val)) : Maybe<&2, Bool>}

# LAW: as_num reads a value as it reads the value with its spans read out
law as_num_same:
  for +val: V.Json
  {Ezjson.as_num(val) == Ezjson.as_num(D1.own(val)) : Maybe<&2, String>}

# LAW: as_u32 reads a value as it reads the value with its spans read out
law as_u32_same:
  for +val: V.Json
  {Ezjson.as_u32(val) == Ezjson.as_u32(D1.own(val)) : Maybe<&2, U32>}

# LAW: as_f32 reads a value as it reads the value with its spans read out
law as_f32_same:
  for +val: V.Json
  {Ezjson.as_f32(val) == Ezjson.as_f32(D1.own(val)) : Maybe<&2, F32>}
