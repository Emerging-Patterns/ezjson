# For every number value whose text is `s`: when `F32.read(s)` is `Some{x}`
# with `F32.abs(x)` at most 3.4028235e38 (the largest finite F32), `as_f32` is
# `Some{x}`; when that read is infinite or `None`, `as_f32` is `None`
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson

# LAW: a number whose F32 read is finite reads as that F32
law as_f32_fits:
  for +raw: String
  for +xx: F32
  for h_read: {F32.read(raw) == Some{xx} : Maybe<&2, F32>}
  for h_fin: {F32.is_le(F32.abs(xx), 3.4028235e38) == True{} : Bool}
  {Ezjson.as_f32(V.JNum{raw}) == Some{xx} : Maybe<&2, F32>}

# LAW: a number too large for F32 reads as none, not as an infinity
law as_f32_overflow:
  for +raw: String
  for +xx: F32
  for h_read: {F32.read(raw) == Some{xx} : Maybe<&2, F32>}
  for h_inf: {F32.is_le(F32.abs(xx), 3.4028235e38) == False{} : Bool}
  {Ezjson.as_f32(V.JNum{raw}) == None{} : Maybe<&2, F32>}

# LAW: a number F32 cannot read reads as none
law as_f32_unread:
  for +raw: String
  for h_read: {F32.read(raw) == None{} : Maybe<&2, F32>}
  {Ezjson.as_f32(V.JNum{raw}) == None{} : Maybe<&2, F32>}
